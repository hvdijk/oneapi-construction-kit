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

#include <compiler/utils/attributes.h>
#include <compiler/utils/metadata_analysis.h>

using namespace llvm;

namespace compiler {
namespace utils {

AnalysisKey GenericMetadataAnalysis::Key;

static Printable printGenericMD(const handler::GenericMetadata &MD) {
  return Printable([MD](raw_ostream &Out) {
    Out << "Kernel Name: " << MD.kernel_name << "\n";
    Out << "Source Name: " << MD.source_name << "\n";
    Out << "Local Memory: " << MD.local_memory_usage << "\n";
    Out << "Sub-group Size: " << print(MD.sub_group_size) << "\n";
  });
}

GenericMetadataAnalysis::Result GenericMetadataAnalysis::run(
    Function &Fn, FunctionAnalysisManager &) {
  auto local_memory_usage = getLocalMemoryUsage(Fn).value_or(0);
  auto kernel_name = Fn.getName().str();
  auto source_name = getOrigFnNameOrFnName(Fn).str();

  auto sub_group_size =
      FixedOrScalableQuantity<uint32_t>(getMuxSubgroupSize(Fn),
                                        /*scalable*/ false);
  // Whole-function vectorization multiplies the apparent sub-group size. If
  // the function doesn't explicitly use sub-groups, though, then keep the
  // size at the mux sub-group size as it's legally compatible with more
  // work-group sizes.
  if (auto vf_info = parseWrapperFnMetadata(Fn);
      !hasNoExplicitSubgroups(Fn) && vf_info) {
    const auto vf = vf_info->first.vf;
    sub_group_size = FixedOrScalableQuantity<uint32_t>(
        sub_group_size.getFixedValue() * vf.getKnownMinValue(),
        vf.isScalable());
  }
  return Result(kernel_name, source_name, local_memory_usage, sub_group_size);
}

PreservedAnalyses GenericMetadataPrinterPass::run(Function &F,
                                                  FunctionAnalysisManager &AM) {
  const handler::GenericMetadata md = AM.getResult<GenericMetadataAnalysis>(F);
  OS << "Cached generic metadata analysis:\n";
  OS << printGenericMD(md);
  return PreservedAnalyses::all();
}

static Printable printVectorizeMD(const handler::VectorizeInfoMetadata &MD) {
  return Printable([MD](raw_ostream &Out) {
    Out << printGenericMD(MD);
    Out << "Min Work Width: " << print(MD.min_work_item_factor) << "\n";
    Out << "Preferred Work Width: " << print(MD.pref_work_item_factor) << "\n";
  });
}

AnalysisKey VectorizeMetadataAnalysis::Key;

VectorizeMetadataAnalysis::Result VectorizeMetadataAnalysis::run(
    Function &Fn, FunctionAnalysisManager &AM) {
  handler::GenericMetadata &GenericMD =
      AM.getResult<GenericMetadataAnalysis>(Fn);

  auto min_width = FixedOrScalableQuantity<uint32_t>::getOne();
  auto pref_width = FixedOrScalableQuantity<uint32_t>::getOne();

  if (auto vf_info = parseWrapperFnMetadata(Fn)) {
    const auto main_vf = vf_info->first.vf;
    pref_width = FixedOrScalableQuantity<uint32_t>(main_vf.getKnownMinValue(),
                                                   main_vf.isScalable());
    // Until we parse the tail, assume this also constitutes the minimum legal
    // width. Unless we're vector predicated, in which case we know we can
    // still execute any amount of work-items.
    if (!vf_info->first.IsVectorPredicated) {
      min_width = pref_width;
    }

    // Now check the tail, which may loosen the requirements on the minimum
    // legal width.
    if (auto tail_info = vf_info->second) {
      const auto tail_vf = tail_info->vf;
      if (tail_info->IsVectorPredicated) {
        // Vector-predicated kernels can execute a minimum of 1 work-item.
        min_width = FixedOrScalableQuantity<uint32_t>::getOne();
      } else {
        min_width = FixedOrScalableQuantity<uint32_t>(
            tail_vf.getKnownMinValue(), tail_vf.isScalable());
      }
    }
  }
  return Result(std::move(GenericMD.kernel_name),
                std::move(GenericMD.source_name), GenericMD.local_memory_usage,
                GenericMD.sub_group_size, min_width, pref_width);
}

PreservedAnalyses VectorizeMetadataPrinterPass::run(
    Function &F, FunctionAnalysisManager &AM) {
  const handler::VectorizeInfoMetadata md =
      AM.getResult<VectorizeMetadataAnalysis>(F);
  OS << "Cached vectorize metadata analysis:\n";
  OS << printVectorizeMD(md);
  return PreservedAnalyses::all();
}

}  // namespace utils
}  // namespace compiler
