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

#include "Common.h"
#include "kts/vecz_tasks_common.h"

using namespace kts::ucl;

TEST_P(Execution, Task_04_01_Copy_Constant_Offset) {
  const unsigned offset = 4;
  kts::Reference1D<cl_int> refOut = [&](size_t x) {
    return (x >= offset) ? kts::Ref_A(x - offset) : 0;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N + offset, refOut);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_04_02_Copy_Uniform_Offset) {
  const cl_int offset = 7;
  const cl_uint offset2 = static_cast<cl_uint>(offset) * 4;
  kts::Reference1D<cl_int> refOut = [&](size_t x) {
    return (x >= offset2) ? kts::Ref_A(x - offset2) : 0;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N + offset2, refOut);
  AddPrimitive(offset);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_04_03_Mul_FMA_Uniform_Offset_Load) {
  const cl_int numMergedArgs = 3;
  kts::Reference1D<cl_int> refIn = [](size_t x) {
    const size_t argID = static_cast<cl_int>(x / kts::N);
    const cl_int srcID = static_cast<cl_int>(x % kts::N);
    switch (argID) {
      default:
      case 0:
        return kts::Ref_PlusOne(srcID);
      case 1:
        return kts::Ref_MinusOne(srcID);
      case 2:
        return kts::Ref_Triple(srcID);
    }
  };

  AddInputBuffer(kts::N * numMergedArgs, refIn);
  AddOutputBuffer(kts::N, kts::Ref_Mul);
  AddOutputBuffer(kts::N, kts::Ref_FMA);
  RunGeneric1D(kts::N, kts::localN);
}

TEST_P(Execution, Task_04_04_Mul_FMA_Uniform_Offset_Store) {
  const cl_int numMergedArgs = 2;
  kts::Reference1D<cl_int> refOut = [](size_t x) {
    const size_t argID = static_cast<cl_int>(x / kts::N);
    const cl_int srcID = static_cast<cl_int>(x % kts::N);
    switch (argID) {
      default:
      case 0:
        return kts::Ref_Mul(srcID);
      case 1:
        return kts::Ref_FMA(srcID);
    }
  };

  AddInputBuffer(kts::N, kts::Ref_PlusOne);
  AddInputBuffer(kts::N, kts::Ref_MinusOne);
  AddInputBuffer(kts::N, kts::Ref_Triple);
  AddOutputBuffer(kts::N * numMergedArgs, refOut);
  RunGeneric1D(kts::N, kts::localN);
}

TEST_P(Execution, Task_04_05_Scatter) {
  kts::Reference1D<cl_int> refOut = [](size_t x) {
    return !kts::Ref_Odd(x) ? kts::Ref_A(x / 2) : 0;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N * 2, refOut);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_04_06_Gather) {
  kts::Reference1D<cl_int> refOut = [](size_t x) { return kts::Ref_A(x * 2); };
  AddInputBuffer(kts::N * 2, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_04_07_Mul_FMA_Uniform_Addr_Load) {
  const cl_int numMergedArgs = 3;
  kts::Reference1D<cl_int> refIn = [&](size_t x) {
    const size_t groupSize = kts::localN * numMergedArgs;
    const size_t groupID = x / groupSize;
    const cl_int localID = static_cast<cl_int>(x % groupSize);
    const size_t argID = localID / kts::localN;
    const cl_int srcID =
        static_cast<cl_int>((groupID * kts::localN) + (localID % kts::localN));
    switch (argID) {
      default:
      case 0:
        return kts::Ref_PlusOne(srcID);
      case 1:
        return kts::Ref_MinusOne(srcID);
      case 2:
        return kts::Ref_Triple(srcID);
    }
  };

  AddInputBuffer(kts::N * numMergedArgs, refIn);
  AddOutputBuffer(kts::N, kts::Ref_Mul);
  AddOutputBuffer(kts::N, kts::Ref_FMA);
  RunGeneric1D(kts::N, kts::localN);
}

TEST_P(Execution, Task_04_08_Mul_FMA_Uniform_Addr_Store) {
  const cl_int numMergedArgs = 2;
  kts::Reference1D<cl_int> refOut = [&](size_t x) {
    const size_t groupSize = kts::localN * numMergedArgs;
    const size_t groupID = x / groupSize;
    const cl_int localID = static_cast<cl_int>(x % groupSize);
    const size_t argID = localID / kts::localN;
    const cl_int srcID =
        static_cast<cl_int>((groupID * kts::localN) + (localID % kts::localN));
    switch (argID) {
      default:
      case 0:
        return kts::Ref_Mul(srcID);
      case 1:
        return kts::Ref_FMA(srcID);
    }
  };

  AddInputBuffer(kts::N, kts::Ref_PlusOne);
  AddInputBuffer(kts::N, kts::Ref_MinusOne);
  AddInputBuffer(kts::N, kts::Ref_Triple);
  AddOutputBuffer(kts::N * numMergedArgs, refOut);
  RunGeneric1D(kts::N, kts::localN);
}

TEST_P(Execution, Task_04_09_Copy4_Scalarized) {
  AddInputBuffer(kts::N * 4, kts::Ref_A);
  AddOutputBuffer(kts::N * 4, kts::Ref_A);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_04_10_Alloca) {
  AddOutputBuffer(kts::N, kts::Ref_Identity);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_04_11_Byval_Struct) {
  struct my_struct {
    cl_int foo;
    cl_int bar;
    cl_int gee;
  };
  my_struct ms = {2, 1, 2};

  kts::Reference1D<cl_int> refOut = [&ms](size_t idx) {
    const cl_int x = kts::Ref_Identity(idx);
    return (x * ms.foo) + (ms.bar * ms.gee);
  };

  AddOutputBuffer(kts::N, refOut);
  AddPrimitive(ms);
  RunGeneric1D(kts::N);
}

struct work_item {
  cl_uint4 global_id;
  cl_uint4 group_id;
};

namespace kts {

template <>
struct Validator<work_item> {
  bool validate(work_item expected, work_item actual) {
    Validator<cl_uint4> v;
    return v.validate(expected.global_id, actual.global_id) &&
           v.validate(expected.group_id, actual.group_id);
  }

  void print(std::stringstream &s, work_item value) {
    Validator<cl_uint4> v;
    s << "{ global_id = ";
    v.print(s, value.global_id);
    s << ", group_id = ";
    v.print(s, value.group_id);
    s << " }";
  }
};
}  // namespace kts

TEST_P(Execution, Task_04_12_Work_Item) {
  kts::Reference1D<work_item> refOut = [](size_t idx) {
    work_item item;
    item.global_id.s[0] = kts::Ref_Identity(idx);
    item.global_id.s[1] = 0;
    item.global_id.s[2] = 0;
    item.global_id.s[3] = 0;
    item.group_id.s[0] = (cl_uint)(idx / kts::localN);
    item.group_id.s[1] = 0;
    item.group_id.s[2] = 0;
    item.group_id.s[3] = 0;
    return item;
  };

  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N, kts::localN);
}

#define NUM_SAMPLES 16
struct SampleBuffer {
  float samples[NUM_SAMPLES];
};

namespace kts {

template <>
struct Validator<SampleBuffer> {
  bool validate(SampleBuffer expected, SampleBuffer actual) {
    Validator<float> v;
    for (unsigned i = 0; i < NUM_SAMPLES; i++) {
      if (!v.validate(expected.samples[i], actual.samples[i])) {
        return false;
      }
    }
    return true;
  }

  void print(std::stringstream &s, SampleBuffer value) {
    Validator<float> v;
    s << "{";
    for (unsigned i = 0; i < NUM_SAMPLES; i++) {
      if (i > 0) s << ", ";
      v.print(s, value.samples[i]);
    }
    s << " }";
  }
};
}  // namespace kts

TEST_P(Execution, Task_04_13_Struct_Offset) {
  const cl_int numChannels = 2;
  cl_int channelID = 1;
  kts::Reference1D<SampleBuffer> refOut = [&channelID](size_t x) {
    SampleBuffer buffer;
    for (unsigned i = 0; i < NUM_SAMPLES; i++) {
      if (x == static_cast<size_t>(channelID)) {
        buffer.samples[i] = (float)i * (1.0f / NUM_SAMPLES);
      } else {
        buffer.samples[i] = 0.0f;
      }
    }
    return buffer;
  };

  AddOutputBuffer(numChannels, refOut);
  AddPrimitive(channelID);
  RunGeneric1D(NUM_SAMPLES);
}

TEST_P(Execution, Task_04_14_Alloca4) {
  kts::Reference1D<cl_int4> refOut = [](size_t x) {
    const cl_int ix = kts::Ref_Identity(x);
    cl_int4 v;
    v.s[0] = ix;
    v.s[1] = ix;
    v.s[2] = ix;
    v.s[3] = ix;
    return v;
  };

  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N);
}

static void ScatterGather(Execution &e) {
  kts::Reference1D<cl_int> refOffset = [](size_t x) {
    return static_cast<cl_int>(kts::N - 1 - x);
  };

  kts::Reference1D<cl_int> refOut = [&refOffset](size_t x) {
    return kts::Ref_A(static_cast<size_t>(refOffset(x)));
  };

  e.AddInputBuffer(kts::N, kts::Ref_A);
  e.AddOutputBuffer(kts::N, refOut);
  e.AddInputBuffer(kts::N, refOffset);
  e.RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_04_15_Scatter_Offset) { ScatterGather(*this); }

TEST_P(Execution, Task_04_16_Gather_Offset) { ScatterGather(*this); }

TEST_P(Execution, Task_04_17_Local_Array) {
  // Whether or not the kernel will be vectorized at a local size of 1 is
  // dependent on the target.
  fail_if_not_vectorized_ = false;

  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, kts::Ref_A);
  RunGeneric1D(kts::N, 1);  // Kernel has local array of size 1.
}

TEST_P(Execution, Task_04_18_Private_Array) {
  unsigned iterations = 16;
  kts::Reference1D<cl_int> refOut = [&iterations](size_t) {
    cl_int sum = 0;
    for (unsigned i = 0; i < iterations; i++) {
      sum += kts::Ref_A(i);
    }
    return sum;
  };

  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N);
}
