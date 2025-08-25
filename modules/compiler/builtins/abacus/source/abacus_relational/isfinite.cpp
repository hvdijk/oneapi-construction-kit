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

#include <abacus/abacus_detail_cast.h>
#include <abacus/abacus_detail_relational.h>
#include <abacus/abacus_relational.h>

namespace {
template <typename T>
struct helper {
  typedef typename TypeTraits<T>::SignedType type;
};

#ifdef __CA_BUILTINS_DOUBLE_SUPPORT
template <>
struct helper<abacus_double> {
  typedef abacus_int type;
};
#endif  // __CA_BUILTINS_DOUBLE_SUPPORT

#ifdef __CA_BUILTINS_HALF_SUPPORT
template <>
struct helper<abacus_half> {
  typedef abacus_int type;
};
#endif
}  // namespace

#define DEF(TYPE)                                             \
  helper<TYPE>::type ABACUS_API __abacus_isfinite(TYPE x) {   \
    return abacus::detail::cast::convert<helper<TYPE>::type>( \
        abacus::detail::relational::isfinite(x));             \
  }

#ifdef __CA_BUILTINS_HALF_SUPPORT
DEF(abacus_half)
DEF(abacus_half2)
DEF(abacus_half3)
DEF(abacus_half4)
DEF(abacus_half8)
DEF(abacus_half16)
#endif

DEF(abacus_float)
DEF(abacus_float2)
DEF(abacus_float3)
DEF(abacus_float4)
DEF(abacus_float8)
DEF(abacus_float16)

#ifdef __CA_BUILTINS_DOUBLE_SUPPORT
DEF(abacus_double)
DEF(abacus_double2)
DEF(abacus_double3)
DEF(abacus_double4)
DEF(abacus_double8)
DEF(abacus_double16)
#endif  // __CA_BUILTINS_DOUBLE_SUPPORT
