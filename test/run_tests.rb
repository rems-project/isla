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

def step(str)
  stdout, stderr, status = Open3.capture3("#{str}")
  if status != 0 then
    puts <<OUTPUT
#{"Failed".red}: #{str}
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
  isla = File.expand_path(File.join($TEST_DIR, "../target/release/isla"))
  exit if !File.file?(isla)

  chdir_relative "."
  Dir.chunks ".", 12 do |file|
    next if file !~ /.+\.sail$/

    basename = File.basename(file, ".*")

    step("#{isla_sail} #{file} -o #{basename}")
    step("LD_LIBRARY_PATH=.. #{isla} -a #{basename}.ir -p prop -t 1")
    puts("#{file} #{"ok".green}\n")
  end
end

run_tests
