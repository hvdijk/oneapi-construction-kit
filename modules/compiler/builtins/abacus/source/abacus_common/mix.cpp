// Copyright (C) Codeplay Software Limited
//
// Licensed under the Apache License, Version 2.0 (the "License") with LLVM
// Exceptions; you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://github.com/codeplaysoftware/oneapi-construction-kit/blob/main/LICENSE.txt
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <abacus/abacus_common.h>
#include <abacus/abacus_detail_common.h>

#define DEF(TYPE)                                \
  TYPE __abacus_mix(TYPE x, TYPE y, TYPE a) {    \
    return abacus::detail::common::mix(x, y, a); \
  }
#define DEF2(TYPE, TYPE2)                              \
  TYPE __abacus_mix(TYPE x, TYPE y, TYPE2 a) {         \
    return abacus::detail::common::mix<TYPE>(x, y, a); \
  }

#ifdef __CA_BUILTINS_HALF_SUPPORT
DEF(abacus_half);
DEF(abacus_half2);
DEF(abacus_half3);
DEF(abacus_half4);
DEF(abacus_half8);
DEF(abacus_half16);

DEF2(abacus_half2, abacus_half);
DEF2(abacus_half3, abacus_half);
DEF2(abacus_half4, abacus_half);
DEF2(abacus_half8, abacus_half);
DEF2(abacus_half16, abacus_half);
#endif  // __CA_BUILTINS_HALF_SUPPORT

DEF(abacus_float);
DEF(abacus_float2);
DEF(abacus_float3);
DEF(abacus_float4);
DEF(abacus_float8);
DEF(abacus_float16);

DEF2(abacus_float2, abacus_float);
DEF2(abacus_float3, abacus_float);
DEF2(abacus_float4, abacus_float);
DEF2(abacus_float8, abacus_float);
DEF2(abacus_float16, abacus_float);

#ifdef __CA_BUILTINS_DOUBLE_SUPPORT
DEF(abacus_double);
DEF(abacus_double2);
DEF(abacus_double3);
DEF(abacus_double4);
DEF(abacus_double8);
DEF(abacus_double16);

DEF2(abacus_double2, abacus_double);
DEF2(abacus_double3, abacus_double);
DEF2(abacus_double4, abacus_double);
DEF2(abacus_double8, abacus_double);
DEF2(abacus_double16, abacus_double);
#endif  // __CA_BUILTINS_DOUBLE_SUPPORT
