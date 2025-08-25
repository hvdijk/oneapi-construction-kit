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

/// @file
///
/// @brief Base class and reference counter API for all OpenCL API objects.

#ifndef BENCHCL_ERROR_H_INCLUDED
#define BENCHCL_ERROR_H_INCLUDED

// ASSERT_EQ_ERRCODE is so-named to match the same macro in UnitCL.  The
// 'STATUS' parameter is always evaluated, but the returned error code is only
// compared with 'EXPECTED' (via 'assert') in assert builds.  This is because
// OpenCL functions are used within constructors and destructors in BenchCL,
// there is nothing that can be done with error codes in general.
#ifndef NDEBUG
#define ASSERT_EQ_ERRCODE(EXPECTED, STATUS) assert((EXPECTED) == (STATUS))
#else
#define ASSERT_EQ_ERRCODE(EXPECTED, STATUS) (void)(STATUS)
#endif

#endif  // BENCHCL_ERROR_H_INCLUDED
