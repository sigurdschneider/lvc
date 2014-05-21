#!/usr/bin/ruby
require 'term/ansicolor'
require 'open3'

include Term::ANSIColor

begin
parallel = false

if ARGV.length == 0 || ARGV[0] == "--help" then
	puts "time.sh - command timing script"
	puts "This script reports cpu and real time consumed by the command"
	puts "Usage:"
	puts "\t./time.sh [command]\t\t for usage in single-threaded context"
	puts "\t./time.sh --parallel [command]\t if multiple commands are run concurrently"
	exit false
end

if ARGV[0] == "--parallel" then
	parallel = true
	ARGV.shift
end

cmd = ARGV.join(' ')
mod = ARGV.last
pad = "".ljust(50 - cmd.length)

print "#{Time.now.strftime("%H:%M:%S")} #{blue('>>>')} #{mod}#{parallel ? "\n" : pad}"

start = Time.now
cstdin, cstdout, cstderr, waitthr = Open3.popen3("bash -c \"time #{cmd}\"")
waitthr.join
time = Time.now - start

File.open("#{mod}.time", 'w') do |file|
  file.puts "#{time}"
end


success = waitthr.value.to_i == 0
color = lambda { |s| success ? (green s) : (red s) }

serr = cstderr.read
user = serr.match(/.*user[ \t]*([0123456789]+)m([0123456789\.]+)s.*/m)
sys = serr.match(/.*sys[ \t]*([0123456789]+)m([0123456789\.]+)s.*/m)
cpu = user[1].to_f * 60 + user[2].to_f + sys[1].to_f * 60 + sys[2].to_f

File.open("#{mod}.time", 'w') do |file|
  file.puts "#{cpu}"
end

if !parallel then
  print color.call("#{cpu.round(2)} / #{time.round(2)}"), "\n"
end

sout = cstdout.read
indent = "  "

if !sout.strip.empty? then
	print "#{Time.now.strftime("%H:%M:%S")} ", color.call("==="), " #{mod}#{pad} ", "OUTPUT FOLLOWS" , "\n"
  print sout.gsub!(/^/, '  ')
end

if parallel then
  print "#{Time.now.strftime("%H:%M:%S")} ", color.call("<<<"), " #{mod}#{pad} ", color.call("#{cpu.round(2)} / #{time.round(2)}"), "\n"
end

exit success

rescue SignalException => e
  exit false 
end
