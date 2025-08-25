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

#include <stdint.h>

#include "FuzzCL/arguments.h"
#include "FuzzCL/context.h"

namespace {
const std::string usage = R"(
usage:
    FuzzGenCorpus corpus [options]
    FuzzGenCorpus -h | --help

Required:
    corpus              Path to the corpus folder

Options:
    -d, --device        Select a specific OpenCL device.
    --enable-callbacks  Enable event callbacks in FuzzCL
    -h, --help          Show this screen.
    -v, --verbose       Print each runtime call to stdout
)";

fuzzcl::options_t options;

std::vector<std::vector<unsigned char>> kernel_binaries;
std::vector<const unsigned char *> kernel_binary_pointers;
std::vector<size_t> kernel_binary_sizes;
}  // namespace

extern "C" int LLVMFuzzerInitialize(int *argc, char ***argv) {
  cargo::argument_parser<1> parser(cargo::KEEP_UNRECOGNIZED);

  std::vector<std::string> kernels;
  fuzzcl::list_dir(KERNEL_SOURCE_DIR, kernels);
  // this array will delete the kernel binaries at the end of the scope
  kernel_binaries.reserve(kernels.size());

  // this array only contains pointers to each kernel binaries. It is used to go
  // from std::vector<std::vector<unsigned char>> to const unsigned char**
  // needed by OpenCL
  for (size_t i = 0; i < kernels.size(); i++) {
    kernel_binaries.emplace_back(
        fuzzcl::read_file<unsigned char>(KERNEL_SOURCE_DIR + kernels[i]));
    kernel_binary_pointers.emplace_back(kernel_binaries.back().data());
    kernel_binary_sizes.emplace_back(kernel_binaries.back().size() *
                                     sizeof(unsigned char));
  }

  cargo::string_view device;
  fuzzcl::add_argument(parser, device, "-d=", "--device=");

  bool help = false;
  fuzzcl::add_argument(parser, help, "-h", "--help");

  bool verbose = false;
  fuzzcl::add_argument(parser, verbose, "-v", "--verbose");

  bool callbacks = false;
  fuzzcl::add_argument(parser, callbacks, "--enable-callbacks");

  if (auto error = parser.parse_args(*argc, *argv)) {
    std::cerr << "error: invalid arguments : " << error;
    switch (error) {
      case cargo::success:
        std::cerr << " not_found";
        break;
      case cargo::bad_argument:
        std::cerr << " bad_argument";
        break;
      case cargo::bad_alloc:
        std::cerr << " bad_alloc";
        break;
      default:
        break;
    }
    std::cerr << usage;
    exit(1);
  }

  if (help) {
    std::cerr << usage;
    exit(0);
  }

  options = {callbacks, verbose, cargo::as<std::string>(device)};
  return 0;
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  fuzzcl::fuzz_from_input(data, size, kernel_binary_pointers.data(),
                          kernel_binary_sizes, options);
  return 0;
}
