// Copyright (C) Codeplay Software Limited
//
// Licensed under the Apache License, Version 2.0 (the "License") with LLVM
// Exceptions; you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://github.com/uxlfoundation/oneapi-construction-kit/blob/main/LICENSE.txt
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <base/software_division_pass.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

using namespace llvm;

llvm::PreservedAnalyses compiler::SoftwareDivisionPass::run(
    Function &F, FunctionAnalysisManager &) {
  bool modified = false;
  for (auto &BB : F) {
    for (auto &I : BB) {
      const uint32_t op = I.getOpcode();
      switch (op) {
        default:
          continue;
        case Instruction::SDiv:
        case Instruction::SRem: {
          // For signed division, worst case is INT_MIN / -1, and divide by
          // zero
          Type *const type = I.getType();

          // Compare dividend to INT_MIN
          CmpInst *const topCompare = ICmpInst::Create(
              Instruction::ICmp, ICmpInst::ICMP_EQ, I.getOperand(0),
              ConstantInt::get(
                  type, APInt::getSignedMinValue(type->getScalarSizeInBits())));
          topCompare->insertBefore(I.getIterator());

          // Compare divisor to -1
          CmpInst *const botCompare =
              ICmpInst::Create(Instruction::ICmp, ICmpInst::ICMP_EQ,
                               I.getOperand(1), ConstantInt::get(type, -1));
          botCompare->insertBefore(I.getIterator());

          // Binary And between dividend and divisor comparison checks
          Instruction *const minDivCondition =
              BinaryOperator::Create(Instruction::And, topCompare, botCompare);
          minDivCondition->insertBefore(I.getIterator());

          // Compare divisor to zero for divide by zero error
          CmpInst *const zeroCompare =
              ICmpInst::Create(Instruction::ICmp, ICmpInst::ICMP_EQ,
                               I.getOperand(1), ConstantInt::get(type, 0));
          zeroCompare->insertBefore(I.getIterator());

          // Binary Or between both of the error case checks
          Instruction *const errCondition = BinaryOperator::Create(
              Instruction::Or, zeroCompare, minDivCondition);
          errCondition->insertBefore(I.getIterator());

          // In the case of an error condition set the divisor to +1
          SelectInst *const select = SelectInst::Create(
              errCondition, ConstantInt::get(type, 1), I.getOperand(1));
          select->insertBefore(I.getIterator());

          I.setOperand(1, select);

          modified = true;
          continue;
        }
        case Instruction::UDiv:
        case Instruction::URem: {
          // For all division, need to check for divide by zero
          Type *const type = I.getType();

          // Equality comparison between divisor and zero
          CmpInst *const compare =
              ICmpInst::Create(Instruction::ICmp, ICmpInst::ICMP_EQ,
                               I.getOperand(1), ConstantInt::get(type, 0));
          compare->insertBefore(I.getIterator());

          // If divisor is zero use select to fallback to +1 for divisor.
          SelectInst *const select = SelectInst::Create(
              compare, ConstantInt::get(type, 1), I.getOperand(1));
          select->insertBefore(I.getIterator());

          I.setOperand(1, select);

          modified = true;
          continue;
        }
      }
    }
  }
  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  return modified ? PA : PreservedAnalyses::all();
}
