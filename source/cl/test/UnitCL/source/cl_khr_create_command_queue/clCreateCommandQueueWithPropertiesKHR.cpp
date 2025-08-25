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

class clCreateCommandQueueWithPropertiesKHRTest : public ucl::ContextTest {
 protected:
  void SetUp() override {
    UCL_RETURN_ON_FATAL_FAILURE(ContextTest::SetUp());
    if (!isPlatformExtensionSupported("cl_khr_create_command_queue")) {
      GTEST_SKIP();
    }
    clCreateCommandQueueWithPropertiesKHR =
        reinterpret_cast<clCreateCommandQueueWithPropertiesKHR_fn>(
            clGetExtensionFunctionAddressForPlatform(
                platform, "clCreateCommandQueueWithPropertiesKHR"));
    ASSERT_NE(nullptr, clCreateCommandQueueWithPropertiesKHR);
  }

  clCreateCommandQueueWithPropertiesKHR_fn
      clCreateCommandQueueWithPropertiesKHR = nullptr;
};

TEST_F(clCreateCommandQueueWithPropertiesKHRTest, Default) {
  cl_int error;
  cl_command_queue command_queue =
      clCreateCommandQueueWithPropertiesKHR(context, device, nullptr, &error);
  EXPECT_SUCCESS(error);
  cl_command_queue_properties properties = 0;
  const size_t size = sizeof(properties);
  EXPECT_SUCCESS(clGetCommandQueueInfo(command_queue, CL_QUEUE_PROPERTIES, size,
                                       &properties, nullptr));
  EXPECT_EQ(0, properties);
  ASSERT_SUCCESS(clReleaseCommandQueue(command_queue));
}

TEST_F(clCreateCommandQueueWithPropertiesKHRTest, DefaultProfiling) {
  cl_int error;
  std::array<cl_queue_properties_khr, 3> properties{
      {CL_QUEUE_PROPERTIES, CL_QUEUE_PROFILING_ENABLE, 0}};
  cl_command_queue command_queue = clCreateCommandQueueWithPropertiesKHR(
      context, device, properties.data(), &error);
  size_t size;
  EXPECT_SUCCESS(clGetCommandQueueInfo(command_queue, CL_QUEUE_PROPERTIES, 0,
                                       nullptr, &size));
  EXPECT_EQ(sizeof(cl_command_queue_properties), size);
  cl_command_queue_properties command_queue_properties;
  EXPECT_SUCCESS(clGetCommandQueueInfo(command_queue, CL_QUEUE_PROPERTIES, size,
                                       &command_queue_properties, nullptr));
  EXPECT_EQ(properties[1], command_queue_properties);
  EXPECT_SUCCESS(error);
  ASSERT_SUCCESS(clReleaseCommandQueue(command_queue));
}

TEST_F(clCreateCommandQueueWithPropertiesKHRTest, InvalidContext) {
  cl_int error;
  cl_command_queue command_queue =
      clCreateCommandQueueWithPropertiesKHR(nullptr, device, nullptr, &error);
  ASSERT_EQ_ERRCODE(CL_INVALID_CONTEXT, error);
  ASSERT_EQ(nullptr, command_queue);
}

TEST_F(clCreateCommandQueueWithPropertiesKHRTest, InvalidDevice) {
  cl_int error;
  cl_command_queue command_queue =
      clCreateCommandQueueWithPropertiesKHR(context, nullptr, nullptr, &error);
  ASSERT_EQ_ERRCODE(CL_INVALID_DEVICE, error);
  ASSERT_EQ(nullptr, command_queue);
}

TEST_F(clCreateCommandQueueWithPropertiesKHRTest, InvalidQueueProperties) {
  cl_int error;
  // We don't currently support CL_QUEUE_ON_DEVICE and to get this return
  // value the properties need to be valid but unsupported by the device.
  std::array<cl_queue_properties_khr, 3> properties{
      {CL_QUEUE_PROPERTIES, CL_QUEUE_ON_DEVICE, 0}};
  cl_command_queue command_queue = clCreateCommandQueueWithPropertiesKHR(
      context, device, properties.data(), &error);
  ASSERT_EQ_ERRCODE(CL_INVALID_QUEUE_PROPERTIES, error);
  ASSERT_EQ(nullptr, command_queue);
}

TEST_F(clCreateCommandQueueWithPropertiesKHRTest, InvalidValue) {
  cl_int error;
  std::array<cl_queue_properties_khr, 3> properties{
      {CL_QUEUE_PROPERTIES, 0xFFFFFFFFFFFFFFFF, 0}};
  cl_command_queue command_queue = clCreateCommandQueueWithPropertiesKHR(
      context, device, properties.data(), &error);
  ASSERT_EQ_ERRCODE(CL_INVALID_VALUE, error);
  ASSERT_EQ(nullptr, command_queue);
  properties = {{0xFFFFFFFFFFFFFFFF, 42, 0}};
  command_queue = clCreateCommandQueueWithPropertiesKHR(
      context, device, properties.data(), &error);
  ASSERT_EQ_ERRCODE(CL_INVALID_VALUE, error);
  ASSERT_EQ(nullptr, command_queue);
}
