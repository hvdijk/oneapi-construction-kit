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

class clGetHostTimerTest : public ucl::DeviceTest {
 protected:
  void SetUp() override {
    UCL_RETURN_ON_FATAL_FAILURE(DeviceTest::SetUp());
    if (!UCL::isDeviceVersionAtLeast({3, 0})) {
      GTEST_SKIP();
    }
  }
};

TEST_F(clGetHostTimerTest, NotImplemented) {
  cl_ulong host_timer_resolution{};
  ASSERT_SUCCESS(clGetPlatformInfo(platform, CL_PLATFORM_HOST_TIMER_RESOLUTION,
                                   sizeof(host_timer_resolution),
                                   &host_timer_resolution, nullptr));
  if (0 != host_timer_resolution) {
    // Since we test against other implementations that may implement this
    // but we aren't actually testing the functionality, just skip.
    GTEST_SKIP();
  }
  cl_ulong host_timestamp{};
  ASSERT_EQ_ERRCODE(CL_INVALID_OPERATION,
                    clGetHostTimer(device, &host_timestamp));
}
