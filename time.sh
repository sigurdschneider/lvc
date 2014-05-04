#!/usr/bin/ruby
require 'term/ansicolor'
require 'open3'

include Term::ANSIColor

cmd = ARGV.join(' ')
print "#{green('>>>')} #{cmd}\n"

start = Time.now
#system(cmd)
cstdin, cstdout, cstderr, waitthr = Open3.popen3(cmd)
path = #{ARGV.last}.split('/')
#Process.wait(waitthr.pid)
waitthr.join
time = Time.now - start
File.open("#{ARGV.last}.time", 'w') do |file|
  file.puts "#{time}"
end


success = waitthr.value.to_i == 0
color = lambda { |s| success ? (green s) : (red s) }

print color.call("<<<"), " #{cmd} \t\t ", color.call("#{time.round(2)}"), "\n"
IO.copy_stream(cstdout, STDOUT)
IO.copy_stream(cstderr, STDERR)

exit success 
