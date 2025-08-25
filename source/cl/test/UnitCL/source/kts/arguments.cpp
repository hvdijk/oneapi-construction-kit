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

#include "kts/arguments.h"

kts::ucl::Argument *kts::ucl::ArgumentList::GetArg(unsigned index) {
  if (index >= GetCount()) {
    return nullptr;
  }
  return args_[index].get();
}

kts::BufferDesc kts::ucl::ArgumentList::GetBufferDescForArg(
    unsigned index) const {
  kts::BufferDesc desc = default_desc_;
  if (index < GetCount()) {
    auto &arg = args_[index];
    const kts::BufferDesc &arg_desc = arg->GetBufferDesc();
    if (arg_desc.size_ > 0) desc.size_ = arg_desc.size_;
    if (arg_desc.streamer_) desc.streamer_ = arg_desc.streamer_;
    if (arg_desc.streamer2_) desc.streamer2_ = arg_desc.streamer2_;
  }
  return desc;
}

void kts::ucl::ArgumentList::AddInputBuffer(const kts::BufferDesc &desc) {
  args_.emplace_back(new kts::ucl::Argument(kts::eInputBuffer, args_.size()));
  args_.back()->SetBufferDesc(desc);
}

void kts::ucl::ArgumentList::AddOutputBuffer(const kts::BufferDesc &desc) {
  args_.emplace_back(new kts::ucl::Argument(kts::eOutputBuffer, args_.size()));
  args_.back()->SetBufferDesc(desc);
}

void kts::ucl::ArgumentList::AddInOutBuffer(const kts::BufferDesc &desc) {
  args_.emplace_back(new kts::ucl::Argument(kts::eInOutBuffer, args_.size()));
  args_.back()->SetBufferDesc(desc);
}

void kts::ucl::ArgumentList::AddLocalBuffer(
    kts::ucl::PointerPrimitive *primitive) {
  kts::ucl::ArgumentList::AddPrimitive(primitive);
}

void kts::ucl::ArgumentList::AddPrimitive(kts::Primitive *primitive) {
  args_.emplace_back(new kts::ucl::Argument(kts::ePrimitive, args_.size()));
  args_.back()->SetPrimitive(primitive);
}

void kts::ucl::ArgumentList::AddSampler(cl_bool normalized_coords,
                                        cl_addressing_mode addressing_mode,
                                        cl_filter_mode filter_mode) {
  args_.emplace_back(new kts::ucl::Argument(kts::eSampler, args_.size()));
  args_.back()->SetSamplerDesc(
      SamplerDesc(normalized_coords, addressing_mode, filter_mode));
}

void kts::ucl::ArgumentList::AddInputImage(const cl_image_format &format,
                                           const cl_image_desc &desc,
                                           const kts::BufferDesc &data) {
  args_.emplace_back(new kts::ucl::Argument(kts::eInputImage, args_.size()));
  args_.back()->SetBufferDesc(data);
  args_.back()->SetImageDesc(ImageDesc(format, desc));
}
