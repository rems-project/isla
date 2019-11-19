#!/usr/bin/env ruby

require 'open3'

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

Dir.chdir(File.dirname(__FILE__))

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

Dir.chdir(File.dirname(__FILE__))

def test_smt
  Dir.chunks ".", 12 do |file|
    next if file !~ /.+\.sail$/

    basename = File.basename(file, ".*")

    puts("#{file} #{"ok".green}\n")
  end
end

test_smt
