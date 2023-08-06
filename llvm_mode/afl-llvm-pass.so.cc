/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include <llvm/IR/Metadata.h>
#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

using namespace llvm;

namespace {

class AFLCoveragePass : public PassInfoMixin<AFLCoveragePass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);

  static bool isRequired() { return true; }
};

} // namespace

PreservedAnalyses AFLCoveragePass::run(Module &M, ModuleAnalysisManager &MAM) {

  outs() << "Load AFLCoveragePass::run\n";

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST
              " by <lszekeres@google.com>\n");

  } else
    be_quiet = 1;

  /* Decide instrumentation ratio */

  char *inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");
  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc", 0,
      GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio)
        continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(IRB.getInt32Ty(), AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"),
                           MDNode::get(C, ArrayRef<Metadata *>()));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(PointerType::get(Int8Ty, 0), AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"),
                          MDNode::get(C, ArrayRef<Metadata *>()));
      Value *MapPtrIdx = IRB.CreateGEP(Int8Ty, MapPtr,
                                       IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(Int8Ty, MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"),
                           MDNode::get(C, ArrayRef<Metadata *>()));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"),
                        MDNode::get(C, ArrayRef<Metadata *>()));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"),
                         MDNode::get(C, ArrayRef<Metadata *>()));

      inst_blocks++;
    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks)
      WARNF("No instrumentation targets found.");
    else
      OKF("Instrumented %u locations (%s mode, ratio %u%%).", inst_blocks,
          getenv("AFL_HARDEN")
              ? "hardened"
              : ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN"))
                     ? "ASAN/MSAN"
                     : "non-hardened"),
          inst_ratio);
  }

  return PreservedAnalyses::all();
}

// static void registerAFLPass(const PassManagerBuilder &,
//                             legacy::PassManagerBase &PM) {

//   PM.add(new AFLCoverage());
// }

// static RegisterStandardPasses
//     RegisterAFLPass(PassManagerBuilder::EP_ModuleOptimizerEarly,
//                     registerAFLPass);

// static RegisterStandardPasses
//     RegisterAFLPass0(PassManagerBuilder::EP_EnabledOnOptLevel0,
//                      registerAFLPass);

llvm::PassPluginLibraryInfo getAFLCoveragePluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "AFLCoverage", "v0.1", [](PassBuilder &PB) {
            // Register ModulePass
            PB.registerPipelineStartEPCallback(
                [](llvm::ModulePassManager &PM, OptimizationLevel Level) {
                  PM.addPass(AFLCoveragePass());
                });
            PB.registerPipelineParsingCallback(
                [](StringRef PassName, ModulePassManager &MPM, ...) {
                  if (PassName == "afl-llvm-pass") {
                    MPM.addPass(AFLCoveragePass());
                    return true;
                  }
                  return false;
                });
          }};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getAFLCoveragePluginInfo();
}