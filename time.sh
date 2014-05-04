#!/usr/bin/ruby
require 'term/ansicolor'
require 'open3'

include Term::ANSIColor

begin
parallel = false

if ARGV[0] == "--parallel" then
	parallel = true
	ARGV.shift
end

cmd = ARGV.join(' ')
pad = "".ljust(40 - cmd.length)

print "#{Time.now.strftime("%H:%M:%S")} #{blue('>>>')} #{cmd}#{parallel ? "\n" : pad}"

start = Time.now
#system(cmd)
cstdin, cstdout, cstderr, waitthr = Open3.popen3("bash -c \"time #{cmd}\"")
path = #{ARGV.last}.split('/')
#Process.wait(waitthr.pid)
waitthr.join
time = Time.now - start
File.open("#{ARGV.last}.time", 'w') do |file|
  file.puts "#{time}"
end

success = waitthr.value.to_i == 0
color = lambda { |s| success ? (green s) : (red s) }

serr = cstderr.read
user = serr.match(/.*user[ \t]*([0123456789]+)m([0123456789\.]+)s.*/m)
sys = serr.match(/.*sys[ \t]*([0123456789]+)m([0123456789\.]+)s.*/m)
cpu = user[1].to_f * 60 + user[2].to_f + sys[1].to_f * 60 + sys[2].to_f

if !parallel then
  print color.call("#{cpu.round(2)} / #{time.round(2)}"), "\n"
end

sout = cstdout.read
print sout

if parallel then
  print "#{Time.now.strftime("%H:%M:%S")} ", color.call("<<<"), " #{cmd} \t\t ", color.call("#{cpu.round(2)} / #{time.round(2)}"), "\n"
end

exit success

rescue SignalException => e
  exit false 
end
