#!/usr/bin/env ruby
# SPDX-License-Identifier: MIT
# Read-only provenance/notice checks for the Lean source distribution.
# This does not substitute for auditing extra assets or dependency bundles.
require "digest"
require "json"
require "open3"
require "optparse"

root = File.expand_path("..", __dir__)
upstreams = {}
OptionParser.new do |options|
  options.banner = "Usage: ruby scripts/check_third_party.rb [--upstream NAME=CHECKOUT]"
  options.on("--upstream NAME=CHECKOUT", "Verify the pinned Git objects in an upstream checkout") do |argument|
    name, checkout = argument.split("=", 2)
    abort "Expected NAME=CHECKOUT" if name.nil? || checkout.nil? || checkout.empty?
    upstreams[name] = File.expand_path(checkout)
  end
end.parse!
abort "Unexpected arguments: #{ARGV.join(' ')}" unless ARGV.empty?

manifest = JSON.parse(File.read(File.join(root, "third_party_manifest.json")))
issues = []
check = lambda { |condition, message| issues << message unless condition }
local_path = lambda do |relative|
  absolute = File.expand_path(relative, root)
  abort "Inventory path escapes the Lean directory: #{relative}" unless absolute.start_with?(root + File::SEPARATOR)
  absolute
end
read = lambda do |relative|
  path = local_path.call(relative)
  check.call(File.file?(path), "Missing file: #{relative}")
  File.file?(path) ? File.binread(path).force_encoding(Encoding::UTF_8) : ""
end
git_blob = lambda do |checkout, revision, path|
  output, status = Open3.capture2("git", "-C", checkout, "show", "#{revision}:#{path}")
  check.call(status.success?, "Cannot read pinned upstream blob: #{revision}:#{path}")
  output.force_encoding(Encoding::UTF_8)
end

check.call(manifest.fetch("schema_version") == 1, "Unsupported inventory schema")
notice = read.call(manifest.fetch("notice"))
readme = read.call("README.md")
project_license = manifest.fetch("project_license")
project_license_text = read.call(project_license.fetch("path"))
check.call(project_license.fetch("spdx") == "MIT" && project_license_text.start_with?("MIT License\n"), "Original project contributions must be MIT-licensed")
check.call(Digest::SHA256.hexdigest(project_license_text) == project_license.fetch("sha256"), "Project MIT license text changed")
check.call(project_license_text.include?(project_license.fetch("copyright_notice")), "Missing project copyright notice")
check.call(readme.include?("[MIT License](LICENSE)"), "README must document the project's MIT license")
check.call(readme.gsub(/\s+/, " ").include?("Third-party code retains its own licenses and notices."), "README must preserve third-party license exceptions")
check.call(readme.include?("Third-party code and acknowledgments"), "Missing prominent README acknowledgments")
check.call(readme.include?("[NOTICE](NOTICE)"), "README must link to NOTICE")
check.call(notice.gsub(/\s+/, " ").include?("does not assert authorship or ownership"), "NOTICE must distinguish project and upstream authorship")

components = manifest.fetch("components")
names = components.map { |component| component.fetch("name") }
check.call(names.uniq == names, "Duplicate component names")
(upstreams.keys - names).each { |name| issues << "Unknown upstream component: #{name}" }
all_paths = []
license_records = {}
components.each do |component|
  name = component.fetch("name")
  revision = component.fetch("revision")
  check.call(revision.match?(/\A[0-9a-f]{40}\z/), "Invalid revision for #{name}")
  check.call(notice.include?(component.fetch("repository")) && notice.include?(revision), "Missing source/revision credit for #{name}")
  expected = component.fetch("files").map { |record| record.fetch("path") }.sort
  actual = Dir.glob(File.join(local_path.call(component.fetch("local_directory")), "**", "*.lean"))
    .map { |path| path.delete_prefix(root + "/") }.sort
  check.call(actual == expected, "Vendored inventory drift for #{name}: added=#{actual - expected}; missing=#{expected - actual}")
  check.call(component.fetch("upstream_notice_files").empty?, "Copy and explicitly inventory any newly introduced upstream NOTICE texts for #{name}")

  component.fetch("licenses").each do |license|
    content = read.call(license.fetch("path"))
    check.call(Digest::SHA256.hexdigest(content) == license.fetch("sha256"), "License text changed: #{license.fetch('path')}")
    license.fetch("copyright_notices").each do |line|
      check.call(content.include?(line), "Missing license copyright: #{line}")
    end
    license_records[license.fetch("path")] = license
    next unless upstreams[name]
    original = git_blob.call(upstreams[name], revision, license.fetch("upstream_path"))
    check.call(content.b == original.b, "License differs from pinned upstream: #{license.fetch('path')}")
  end

  component.fetch("files").each do |record|
    all_paths << record.fetch("path")
    source = read.call(record.fetch("path"))
    header = source[0, 2500]
    check.call(header.include?(revision), "Missing revision notice: #{record.fetch('path')}")
    check.call(header.match?(/Ported|Modified for this project/i), "Missing modification notice: #{record.fetch('path')}")
    check.call(header.include?(record.fetch("spdx") == "MIT" ? "MIT" : "Apache"), "Missing license identification: #{record.fetch('path')}")
    record.fetch("retained_notices").each do |line|
      check.call(header.include?(line), "Missing original notice in #{record.fetch('path')}: #{line}")
    end
    license = license_records[record.fetch("license_file")]
    check.call(license && license.fetch("spdx") == record.fetch("spdx"), "Incorrect license mapping: #{record.fetch('path')}")
    if license && license.fetch("spdx") == "MIT"
      license.fetch("copyright_notices").each do |line|
        check.call(header.include?(line), "Missing MIT author credit in #{record.fetch('path')}: #{line}")
      end
    end
    next unless upstreams[name]
    original = git_blob.call(upstreams[name], revision, record.fetch("upstream_path"))
    check.call(Digest::SHA256.hexdigest(original) == record.fetch("upstream_sha256"), "Upstream source hash mismatch: #{record.fetch('path')}")
    original.lines.grep(/^(Copyright|Authors:)/).map(&:strip).each do |line|
      check.call(header.include?(line), "Omitted pinned upstream notice in #{record.fetch('path')}: #{line}")
    end
  end

  next unless upstreams[name]
  tree, status = Open3.capture2("git", "-C", upstreams[name], "ls-tree", "-r", "--name-only", revision)
  check.call(status.success?, "Cannot inspect pinned upstream tree: #{name}")
  original_notices = tree.lines.map(&:chomp).select { |path| File.basename(path).match?(/\ANOTICE(?:[._-].*)?\z/i) }.sort
  check.call(original_notices == component.fetch("upstream_notice_files").sort, "Upstream NOTICE inventory differs: #{name}")
end

manifest.fetch("adaptations").each do |record|
  all_paths << record.fetch("path")
  source = read.call(record.fetch("path"))
  header = source[0, 2500]
  component = components.find { |item| item.fetch("name") == record.fetch("component") }
  check.call(!component.nil?, "Unknown adaptation source: #{record.fetch('path')}")
  next unless component
  check.call(header.include?(component.fetch("revision")), "Missing adaptation revision: #{record.fetch('path')}")
  check.call(header.include?("SPDX-License-Identifier: #{record.fetch('spdx')}"), "Missing adaptation license: #{record.fetch('path')}")
  check.call(header.include?(record.fetch("upstream_path")), "Missing adaptation source path: #{record.fetch('path')}")
  check.call(header.include?("Modified for this project"), "Missing adaptation modification notice: #{record.fetch('path')}")
  record.fetch("retained_notices").each do |line|
    check.call(header.include?(line), "Missing adaptation copyright: #{record.fetch('path')}")
  end
  check.call(license_records.key?(record.fetch("license_file")), "Missing full adaptation license: #{record.fetch('path')}")
  next unless upstreams[record.fetch("component")]
  original = git_blob.call(upstreams[record.fetch("component")], component.fetch("revision"), record.fetch("upstream_path"))
  check.call(Digest::SHA256.hexdigest(original) == record.fetch("upstream_sha256"), "Adaptation source hash mismatch: #{record.fetch('path')}")
end
check.call(all_paths.uniq == all_paths, "Source file appears more than once in the inventory")
manifest.fetch("local_import_wrappers").each do |wrapper|
  check.call(read.call(wrapper).include?("NOTICE"), "Integration wrapper must identify provenance: #{wrapper}")
end
classified = all_paths + manifest.fetch("local_import_wrappers")
Dir.glob(File.join(root, "**", "*.lean")).each do |path|
  relative = path.delete_prefix(root + "/")
  next if relative.start_with?(".lake/") || classified.include?(relative)
  header = File.read(path, encoding: "UTF-8")[0, 2500]
  check.call(!header.match?(/(?:ported|adapted) from|Copyright[^\n]*(?:Samuel Schlesinger|Jesse Alama|Kenny Daniel)/i),
    "Uninventoried third-party source notice: #{relative}")
end

locked = JSON.parse(read.call("lake-manifest.json")).fetch("packages")
expected_dependencies = manifest.fetch("external_dependencies")
check.call(locked.map { |package| package.fetch("name") }.sort == expected_dependencies.map { |package| package.fetch("name") }.sort,
  "External dependency inventory differs from lake-manifest.json")
expected_dependencies.each do |dependency|
  package = locked.find { |item| item.fetch("name") == dependency.fetch("name") }
  next unless package
  check.call(package.fetch("url") == dependency.fetch("repository") && package.fetch("rev") == dependency.fetch("revision"),
    "Dependency provenance drift: #{dependency.fetch('name')}")
  cached_license = File.join(root, ".lake", "packages", dependency.fetch("name"), dependency.fetch("license_path_in_package"))
  next unless File.file?(cached_license)
  check.call(Digest::SHA256.file(cached_license).hexdigest == dependency.fetch("root_license_sha256"),
    "Installed dependency root license changed: #{dependency.fetch('name')}")
end
check.call(read.call("lean-toolchain").strip == manifest.fetch("toolchain"), "Toolchain inventory drift")

unless issues.empty?
  issues.each { |issue| warn "ERROR: #{issue}" }
  abort "Third-party notice audit failed (#{issues.length} issues)."
end
puts "Original project contributions: MIT (LICENSE). Third-party license exceptions retained."
puts "Checked #{components.sum { |component| component.fetch('files').length }} vendored Lean files, " \
  "#{manifest.fetch('adaptations').length} direct adaptation, #{license_records.length} unchanged full licenses, " \
  "and #{expected_dependencies.length} locked external dependencies."
puts "Verified original sources and notices against #{upstreams.length} pinned upstream Git trees." unless upstreams.empty?
