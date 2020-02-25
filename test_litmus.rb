#!/usr/bin/env ruby

require 'open3'
require 'optparse'

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

def step_print(str, *extra)
  stdout, stderr, status = Open3.capture3("#{str}")
  expected = extra.fetch(0, 0)
  if status.exitstatus != expected then
    puts <<OUTPUT
#{"Failed".red} (expected #{expected}, got: #{status}): #{str}
#{"stdout".cyan}: #{stdout}
#{"stderr".blue}: #{stderr}
OUTPUT
    exit
  else
    puts stdout
    exit
  end
end

$options = {}
OptionParser.new do |opts|
  opts.banner = "Usage: example.rb [options]"

  opts.on("-a", "--arch=ARCH", "Architecture (.ir) file") do |arch|
    $options[:arch] = arch
  end

  opts.on("-d", "--dir=PATH", "File containing litmus tests") do |dir|
    $options[:dir] = File.expand_path(dir)
  end

  opts.on("-m", "--model=PATH", "File containing litmus tests") do |model|
    $options[:model] = model
  end
end.parse!

def run_tests
  Dir.chunks $options[:dir], 12 do |file|
    next if file !~ /.+\.litmus$/

    basename = File.basename(file, ".*")

    step("isla-litmus #{$options[:dir]}/#{file} > #{basename}.toml")
    step_print("isla-axiomatic -l #{basename}.toml -a #{$options[:arch]} -m #{$options[:model]} --cache /tmp")
  end
end

run_tests
