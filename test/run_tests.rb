#!/usr/bin/env ruby

require 'open3'

$TEST_DIR = File.expand_path(File.dirname(__FILE__))

class String
  def colorize(color_code)
    "\e[#{color_code}m#{self}\e[0m"
  end

  def red
    colorize(91)
  end

  def green
    colorize(92)
  end

  def yellow
    colorize(93)
  end

  def blue
    colorize(94)
  end

  def cyan
    colorize(96)
  end
end

class Dir
  def self.chunks(dir, n, &block)
    Dir.entries(dir).each_slice(n).each do |chunk|
      chunk.each { |file| fork { yield file } }
      Process.waitall
    end
  end
end

def step(str, *extra)
  stdout, stderr, status = Open3.capture3("#{str}")
  expected = extra.fetch(0, 0)
  if status.exitstatus != expected then
    puts <<OUTPUT
#{"Failed".red} (expected #{expected}, got: #{status}): #{str}
#{"stdout".cyan}: #{stdout}
#{"stderr".blue}: #{stderr}
OUTPUT
    exit
  end
end

def chdir_relative(path)
  Dir.chdir(File.expand_path(File.join($TEST_DIR, path)))
end

def run_tests
  chdir_relative "../isla-sail"
  step "make"
  isla_sail = File.expand_path(File.join($TEST_DIR, "../isla-sail/isla-sail"))
  exit if !File.file?(isla_sail)

  chdir_relative ".."
  step "cargo build --release"
  isla = File.expand_path(File.join($TEST_DIR, "../target/release/isla-property"))
  exit if !File.file?(isla)

  puts "Running tests:".blue

  chdir_relative "."
  Dir.chunks ".", 12 do |file|
    next if file !~ /.+\.sail$/

    basename = File.basename(file, ".*")

    building = Process.clock_gettime(Process::CLOCK_MONOTONIC)
    step("#{isla_sail} #{file} include/config.sail -o #{basename}")
    starting = Process.clock_gettime(Process::CLOCK_MONOTONIC)
    if File.extname(basename) == ".unsat" then
      step("LD_LIBRARY_PATH=.. #{isla} -a #{basename}.ir -p prop -t 2 -c ../configs/plain.toml")
    else
      step("LD_LIBRARY_PATH=.. #{isla} -a #{basename}.ir -p prop -t 2 -c ../configs/plain.toml", 1)
    end
    ending = Process.clock_gettime(Process::CLOCK_MONOTONIC)
    build_time = (starting - building) * 1000
    time = (ending - starting) * 1000
    puts "#{file}".ljust(40).concat("#{"ok".green} (#{build_time.to_i}ms/#{time.to_i}ms)\n")
  end
end

run_tests
