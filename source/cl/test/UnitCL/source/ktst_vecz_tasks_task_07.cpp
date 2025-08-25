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

#include <cstring>

#include "Common.h"
#include "kts/vecz_tasks_common.h"

using namespace kts::ucl;

TEST_P(Execution, Task_07_01_Copy_If_Even_Item) {
  kts::Reference1D<cl_int> refOut = [](size_t x) {
    const cl_int lid = static_cast<cl_int>(x % kts::localN);
    return ((lid & 1) == 0) ? kts::Ref_A(x) : -1;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N, kts::localN);
}

TEST_P(Execution, Task_07_02_Copy_If_Nested_Item) {
  kts::Reference1D<cl_int> refOut = [](size_t x) {
    const cl_int lid = static_cast<cl_int>(x % kts::localN);
    return ((lid & 1) == 0) && ((lid & 2) == 0) ? -kts::Ref_A(x) : 0;
  };
  kts::Reference1D<cl_int> refOut2 = [](size_t x) {
    const cl_int lid = static_cast<cl_int>(x % kts::localN);
    return ((lid & 1) == 0) ? kts::Ref_A(x) : 0;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut);
  AddOutputBuffer(kts::N, refOut2);
  RunGeneric1D(kts::N, kts::localN);
}

TEST_P(Execution, Task_07_03_Add_no_NaN) {
  kts::Reference1D<cl_float> refOut = [](size_t x) {
    const cl_float a = kts::Ref_NegativeOffset(x);
    const cl_float b = kts::Ref_Float(x);
    const bool exclude = stdcompat::isnan(a) || stdcompat::isnan(b);
    return !exclude ? a + b : 0.0f;
  };
  AddInputBuffer(kts::N, kts::Ref_NegativeOffset);
  AddInputBuffer(kts::N, kts::Ref_Float);
  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N, kts::localN);
}

TEST_P(Execution, Task_07_04_Convolution) {
  const cl_int FILTER_SIZE = 1;
  kts::Reference1D<cl_float> refOut = [&](size_t x) {
    const cl_int v = kts::Ref_Identity(x);
    if (((v - FILTER_SIZE) < 0) || ((v + FILTER_SIZE) >= (cl_int)kts::N)) {
      return 0.0f;
    }
    cl_float sum = 0.0f;
    cl_float totalWeight = 0.0f;
    for (cl_int i = -FILTER_SIZE; i <= FILTER_SIZE; i++) {
      const cl_float weight(static_cast<cl_float>(x - i));
      totalWeight += weight;
      sum += weight * kts::Ref_NegativeOffset(x + i);
    }
    sum /= totalWeight;
    return sum;
  };
  AddMacro("FILTER_SIZE", FILTER_SIZE);
  AddInputBuffer(kts::N, kts::Ref_NegativeOffset);
  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_07_05_Ternary_Pointer) {
  AddInputBuffer(kts::N, kts::Ref_Odd);
  AddInputBuffer(kts::N, (kts::Reference1D<cl_int>)([](size_t) { return 1; }));
  AddInputBuffer(kts::N, (kts::Reference1D<cl_int>)([](size_t) { return -1; }));
  AddOutputBuffer(kts::N, kts::Ref_Ternary);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_07_06_Copy_If_Even_Item_Phi) {
  kts::Reference1D<cl_int> refOut = [](size_t x) {
    const cl_int lid = static_cast<cl_int>(x % kts::localN);
    return ((lid & 1) == 0) ? kts::Ref_A(x) : -1;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N, kts::localN);
}

TEST_P(Execution, Task_07_07_Masked_Loop_Uniform) {
  cl_int n = 16;
  kts::Reference1D<cl_int> refOut = [&n](size_t x) {
    if ((x < 2) || (x > 6)) return 0;
    cl_int sum = 0;
    for (cl_int i = 0; i < n; i++) {
      sum += kts::Ref_A(i);
    }
    return sum;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut);
  AddPrimitive(n);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_07_08_Masked_Loop_Varying) {
  cl_int n = 16;
  kts::Reference1D<cl_int> refOut = [&n](size_t x) {
    if ((size_t)(x + n) > kts::N) return 0;
    cl_int sum = 0;
    for (cl_int i = 0; i < n; i++) {
      sum += kts::Ref_A(x + i);
    }
    return sum;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut);
  AddPrimitive(n);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_07_09_Control_Dep_Packetization) {
  // Test with the first constant that exercises one path.
  const unsigned C1 = 1;
  const unsigned N1 = (unsigned)kts::N;
  kts::Reference1D<cl_int> refOut1 = [=](size_t x) {
    if (x != C1) {
      return kts::Ref_A(x) * 2;
    } else {
      return 0;
    }
  };

  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut1);
  AddPrimitive(C1);
  RunGeneric1D(N1, kts::localN);

  // Test with the second constant that exercises the other path.
  const unsigned C2 = (unsigned)kts::N + 1;
  const unsigned N2 = (unsigned)kts::N;
  kts::Reference1D<cl_int> refOut2 = [=](size_t x) {
    if (x != C2) {
      return kts::Ref_A(x) * 2;
    } else {
      return 0;
    }
  };

  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut2);
  AddPrimitive(C2);
  RunGeneric1D(N2, kts::localN);
}

TEST_P(Execution, Task_07_10_Control_Dep_Scalarization) {
  const unsigned N1 = (unsigned)kts::N;
  kts::Reference1D<cl_int4> refOut1 = [=](size_t x) {
    cl_int4 res{{0, 0, 0, 0}};
    if (x % 4 == 0) {
      res.s[0] = kts::Ref_A(x + 0) * 2;
      res.s[1] = kts::Ref_A(x + 1) * 2;
      res.s[2] = kts::Ref_A(x + 2) * 2;
      res.s[3] = kts::Ref_A(x + 3) * 2;
    }
    return res;
  };

  AddInputBuffer(kts::N * 4, kts::Ref_A);
  AddOutputBuffer(kts::N * 4, refOut1);
  RunGeneric1D(N1, kts::localN);

  const unsigned N2 = (unsigned)kts::N;
  kts::Reference1D<cl_int4> refOut2 = [=](size_t x) {
    cl_int4 res{{0, 0, 0, 0}};
    if (x % 4 == 0) {
      res.s[0] = kts::Ref_A(x + 0) * 2;
      res.s[1] = kts::Ref_A(x + 1) * 2;
      res.s[2] = kts::Ref_A(x + 2) * 2;
      res.s[3] = kts::Ref_A(x + 3) * 2;
    }
    return res;
  };

  AddInputBuffer(kts::N * 4, kts::Ref_A);
  AddOutputBuffer(kts::N * 4, refOut2);
  RunGeneric1D(N2, kts::localN);
}

TEST_P(Execution, Task_07_11_Copy_If_Even_Item_Early_Return) {
  kts::Reference1D<cl_int> refOut = [](size_t x) {
    const cl_int lid = static_cast<cl_int>(x % kts::localN);
    return ((lid & 1) == 0) ? kts::Ref_A(x) : -1;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N, kts::localN);
}

TEST_P(Execution, Task_07_12_Scalar_Masked_Load) {
  // Test with the first constant that exercises one path.
  const unsigned C1 = 1;
  const unsigned N1 = (unsigned)kts::N;
  kts::Reference1D<cl_int> refOut1 = [=](size_t x) {
    if ((unsigned)x == C1) {
      return kts::Ref_A(0) * 2;
    } else {
      return 0;
    }
  };

  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut1);
  AddPrimitive(C1);
  RunGeneric1D(N1);

  // Test with the second constant that exercises the other path.
  const unsigned C2 = (unsigned)kts::N + 1;
  const unsigned N2 = (unsigned)kts::N;
  kts::Reference1D<cl_int> refOut2 = [&C2](size_t x) {
    if ((unsigned)x == C2) {
      return kts::Ref_A(0) * 2;
    } else {
      return 0;
    }
  };

  AddInputBuffer(kts::N, kts::Ref_A);
  AddOutputBuffer(kts::N, refOut2);
  AddPrimitive(C2);
  RunGeneric1D(N2, kts::localN);
}

static void TestScalarMaskedStore(Execution *e, bool isUniform = true) {
  // Test with the first constant that exercises one path.
  const unsigned C1 = 1;
  const unsigned N1 = (unsigned)kts::N;
  kts::Reference1D<cl_int> refOut1 = [=](size_t x) {
    if (x != C1) {
      return (cl_int)(C1 + (isUniform ? 0 : x));
    } else {
      return 0;
    }
  };

  e->AddOutputBuffer(kts::N, refOut1);
  e->AddPrimitive(C1);
  e->RunGeneric1D(N1, kts::localN);

  // Test with the second constant that exercises the other path.
  const unsigned C2 = (unsigned)kts::N + 1;
  const unsigned N2 = (unsigned)kts::N;
  kts::Reference1D<cl_int> refOut2 = [=](size_t x) {
    if (x != C2) {
      return (cl_int)(C2 + (isUniform ? 0 : x));
    } else {
      return 0;
    }
  };

  e->AddOutputBuffer(kts::N, refOut2);
  e->AddPrimitive(C2);
  e->RunGeneric1D(N2, kts::localN);
}

TEST_P(Execution, Task_07_13_Scalar_Masked_Store_Uniform) {
  TestScalarMaskedStore(this);
}

TEST_P(Execution, Task_07_14_Scalar_Masked_Store_Varying) {
  TestScalarMaskedStore(this, false);
}

TEST_P(Execution, Task_07_15_Normalize_Range) {
  cl_int bound = 16;
  kts::Reference1D<cl_int> refIn = [](size_t x) {
    return kts::Ref_Identity(x) - 33;
  };
  kts::Reference1D<cl_int> refOut = [&refIn, &bound](size_t x) {
    cl_int val = refIn(x);
    do {
      val += bound;
    } while (val < 0);
    return val;
  };
  AddInputBuffer(kts::N, refIn);
  AddOutputBuffer(kts::N, refOut);
  AddPrimitive(bound);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_07_16_Normalize_Range_While) {
  cl_int bound = 16;
  kts::Reference1D<cl_int> refIn = [](size_t x) {
    return kts::Ref_Identity(x) - 33;
  };
  kts::Reference1D<cl_int> refOut = [&refIn, &bound](size_t x) {
    cl_int val = refIn(x);
    while (val < 0) {
      val += bound;
    }
    return val;
  };
  AddInputBuffer(kts::N, refIn);
  AddOutputBuffer(kts::N, refOut);
  AddPrimitive(bound);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_07_17_If_In_Loop) {
  kts::Reference1D<cl_int> refOut = [](size_t x) {
    cl_int sum = 0;
    for (size_t i = 0; i <= x; i++) {
      cl_int val;
      if (i & 1) {
        val = kts::Ref_B(x) * 2;
      } else {
        val = kts::Ref_A(x) * 3;
      }
      sum += val;
    }
    return sum;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddInputBuffer(kts::N, kts::Ref_B);
  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_07_18_If_In_Uniform_Loop) {
  kts::Reference1D<cl_int> refOut = [](size_t x) {
    cl_int sum = 0;
    for (cl_int i = 0; i < (cl_int)kts::N; i++) {
      cl_int val;
      if (x & 1) {
        val = kts::Ref_B(i) * 2;
      } else {
        val = kts::Ref_A(i) * 3;
      }
      sum += val;
    }
    return sum;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddInputBuffer(kts::N, kts::Ref_B);
  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_07_19_Nested_Loops) {
  cl_int height = (cl_int)kts::N / 2, width = (cl_int)kts::N / 2;
  kts::Reference1D<cl_int> refStrides = [](size_t x) {
    return 1 + (kts::Ref_Identity(x) % 4);
  };
  kts::Reference1D<cl_int> refOut = [&height, &width, &refStrides](size_t x) {
    cl_int sum = 0;
    const cl_int strideX = refStrides(x);
    for (size_t j = 0; j < (size_t)height; j++) {
      for (size_t i = 0; i < (size_t)width; i += strideX) {
        sum += kts::Ref_A((cl_int)((j * width) + i));
      }
    }
    return sum;
  };
  AddInputBuffer(kts::N * kts::N, kts::Ref_A);
  AddInputBuffer(kts::N, refStrides);
  AddOutputBuffer(kts::N, refOut);
  AddPrimitive(width);
  AddPrimitive(height);
  RunGeneric1D(kts::N);
}

TEST_P(Execution, Task_07_20_Sibling_Loops) {
  kts::Reference1D<cl_int> refOut = [](size_t x) {
    cl_int sum = 0;
    const cl_int ix = kts::Ref_Identity(x);
    for (cl_int i = 0; i <= ix; i++) {
      cl_int val;
      if (i & 1) {
        val = kts::Ref_B(i) * 2;
      } else {
        val = kts::Ref_A(i) * 3;
      }
      sum += val;
    }
    for (cl_int i = ix + 1; i < (cl_int)kts::N; i++) {
      cl_int val;
      if (i & 1) {
        val = kts::Ref_A(i) * -5;
      } else {
        val = kts::Ref_B(i) * 17;
      }
      sum += val;
    }
    return sum;
  };
  AddInputBuffer(kts::N, kts::Ref_A);
  AddInputBuffer(kts::N, kts::Ref_B);
  AddOutputBuffer(kts::N, refOut);
  RunGeneric1D(kts::N);
}

static void TestHalfToFloat(Execution *e) {
  const size_t numSamples = 32;
  const cl_ushort inputs[numSamples] = {
      // Values required to reproduce #7163.
      // First value is zero, remaining are denormals.
      0x0000, 0x0001, 0x0002, 0x0003, 0x0004, 0x0005, 0x0006, 0x0007, 0x0008,
      0x0009, 0x000a, 0x000b, 0x000c, 0x000d, 0x000e, 0x000f,

      // Mixing normals and denormals.
      0x0001, 0x000a, 0x4015, 0xc0bf, 0x0004, 0x4042, 0xc023, 0x000f,

      // Zeroes.
      0x0000, 0x8000,

      // Normals.
      0x4001, 0xc001,

      // Infinites.
      0x7c00, 0xfc00,

      // NaNs.
      0x7c01, 0xfc01};
  const cl_uint outputs[numSamples] = {
      0x00000000, 0x33800000, 0x34000000, 0x34400000, 0x34800000, 0x34a00000,
      0x34c00000, 0x34e00000, 0x35000000, 0x35100000, 0x35200000, 0x35300000,
      0x35400000, 0x35500000, 0x35600000, 0x35700000,

      0x33800000, 0x35200000, 0x4002a000, 0xc017e000, 0x34800000, 0x40084000,
      0xc0046000, 0x35700000, 0x00000000, 0x80000000, 0x40002000, 0xc0002000,
      0x7f800000, 0xff800000, 0x7f802000, 0xff802000};

  kts::Reference1D<cl_ushort> refIn = [=, &inputs](size_t x) {
    return x < numSamples ? inputs[x] : 0;
  };
  kts::Reference1D<cl_uint> refOut = [&outputs](size_t x, cl_uint r) {
    float result;
    memcpy(&result, &r, sizeof(result));
    return ((x == 30 || x == 31) && stdcompat::isnan(result)) ||
           r == outputs[x];
  };
  e->AddInputBuffer(numSamples, refIn);
  e->AddOutputBuffer(numSamples, refOut);
  e->RunGeneric1D(numSamples);
}

TEST_P(Execution, Task_07_21_Convert_Half_To_Float_Impl) {
  TestHalfToFloat(this);
}

TEST_P(Execution, Task_07_22_Convert_Half_To_Float_Builtin) {
  TestHalfToFloat(this);
}

TEST_P(Execution, Task_07_23_Convert_Half_To_Float_Nested_Ifs) {
  TestHalfToFloat(this);
}

TEST_P(Execution, Task_07_24_Convert_Half_To_Float_VLoad) {
  TestHalfToFloat(this);
}
