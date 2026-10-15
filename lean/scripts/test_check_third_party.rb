#!/usr/bin/env ruby
# SPDX-License-Identifier: MIT
# Negative regression checks. Faults are injected into reads in a subprocess;
# no source, license, inventory, or cached dependency file is modified.
require "open3"
require "rbconfig"

root = File.expand_path("..", __dir__)
auditor = File.join(__dir__, "check_third_party.rb")
output, status = Open3.capture2e(RbConfig.ruby, auditor, chdir: root)
abort "Baseline audit failed:\n#{output}" unless status.success?

read_hook = <<~'RUBY'
  class << File
    alias_method :notice_test_original_binread, :binread
    def binread(path, *arguments)
      content = notice_test_original_binread(path, *arguments)
      return content unless path.to_s.end_with?(ENV.fetch("FAITHFULNESS_NOTICE_TEST_PATH"))
      content.sub(ENV.fetch("FAITHFULNESS_NOTICE_TEST_FIND"), ENV.fetch("FAITHFULNESS_NOTICE_TEST_REPLACE"))
    end
  end
RUBY
cases = [
  ["changed project MIT license", File.join(root, "LICENSE"), "MIT License", "CHANGED LICENSE", "Original project contributions must be MIT-licensed"],
  ["omitted third-party license exception", "/README.md", "Third-party code retains its own licenses and notices.", "EXCEPTION REMOVED", "README must preserve third-party license exceptions"],
  ["omitted original copyright", "/Cslib/Init.lean", "Copyright (c) 2025 Jesse Alama. All rights reserved.", "REMOVED", "Missing original notice"],
  ["omitted adaptation credit", "/TalBlockAdvice.lean", "Copyright (c) 2026 Samuel Schlesinger. All rights reserved.", "REMOVED", "Missing adaptation copyright"],
  ["omitted multiplier credit", "/IntegerMultBounds/Machine.lean", "Copyright (c) 2026 Kenny Daniel", "REMOVED", "Missing MIT author credit"],
  ["changed full license", "/IntegerMultBounds/LICENSE", "MIT License", "CHANGED LICENSE", "License text changed"],
  ["dependency pin drift", "/lake-manifest.json", "c44e0c8ee63ca166450922a373c7409c5d26b00b", "0" * 40, "Dependency provenance drift"]
]
cases.each do |name, suffix, find, replacement, expected|
  environment = {
    "FAITHFULNESS_NOTICE_TEST_PATH" => suffix,
    "FAITHFULNESS_NOTICE_TEST_FIND" => find,
    "FAITHFULNESS_NOTICE_TEST_REPLACE" => replacement
  }
  code = read_hook + "\nARGV.clear\nload #{auditor.dump}\n"
  output, status = Open3.capture2e(environment, RbConfig.ruby, "-e", code, chdir: root)
  abort "Audit did not reject #{name}:\n#{output}" unless status.exitstatus == 1 && output.include?(expected)
end

inventory_hook = <<~'RUBY'
  class << Dir
    alias_method :notice_test_original_glob, :glob
    def glob(pattern, *arguments, &block)
      result = notice_test_original_glob(pattern, *arguments, &block)
      if pattern.to_s.end_with?("/Cslib/**/*.lean")
        result + [File.join(File.dirname(File.dirname(pattern.to_s)), "Unacknowledged.lean")]
      else
        result
      end
    end
  end
RUBY
output, status = Open3.capture2e(RbConfig.ruby, "-e", inventory_hook + "\nARGV.clear\nload #{auditor.dump}\n", chdir: root)
abort "Audit did not reject vendored inventory drift:\n#{output}" unless status.exitstatus == 1 && output.include?("Vendored inventory drift for cslib")
puts "Baseline and #{cases.length + 1} negative notice-audit regression checks passed; no files modified."
