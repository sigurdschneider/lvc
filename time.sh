#!/usr/bin/ruby

start = Time.now
system(ARGV.join(' '))
path = #{ARGV.last}.split('/')
File.open("#{ARGV.last}.time", 'w') do |file|
  file.puts "#{Time.now - start}"
end
