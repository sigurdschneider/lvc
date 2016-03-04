#!/usr/bin/ruby21
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
timefile = mod.gsub(/(.*)(\/)(.*)/, '\1/.\3') + ".time"
pad = "".ljust(30 - mod.length)

est = File.readable?(timefile) ? File.read(timefile) : ""
eta = (Time.now + est.to_i).strftime("%H:%M:%S")
pad2 = "".ljust(19 - est.strip.length)
eststr = "#{cyan(est.strip)}#{pad2}" + (parallel ? (est.strip == "" ? blue("ETA unavailable") : "ETA #{eta}") : "")
timestamp = Time.now.strftime("%H:%M:%S") 
print "#{timestamp} #{cyan('>>>')} #{mod}#{pad}#{eststr}#{(parallel ? "\n" : "")}"

start = Time.now
cstdin, cstdout, cstderr, waitthr = Open3.popen3("bash -c \"time #{cmd}\"")
waitthr.join
time = Time.now - start
success = waitthr.value.to_i == 0
color = lambda { |s| success ? (green s) : (red s) }
serr = cstderr.read
user = serr.match(/.*user[ \t]*([0123456789]+)m([0123456789\.]+)s.*/m)
sys = serr.match(/.*sys[ \t]*([0123456789]+)m([0123456789\.]+)s.*/m)
cpu = user[1].to_f * 60 + user[2].to_f + sys[1].to_f * 60 + sys[2].to_f
timing = "#{cpu.round(2)} / #{time.round(2)}"
pad2 = "".ljust(19 - timing.length)
changesec = (time - est.to_f)
changesecstr = "%+.2f" % changesec 
change = est == "" ? blue("n/a") : (changesec <= 0 ? green(changesecstr) : red(changesecstr))
line_count = `wc -l "#{mod}.v"`.strip.split(' ')[0].to_i
spl = (line_count / cpu).round(0)
speed = success ? ("#{line_count} L,".rjust(9) + "#{spl} L/s".rjust(8)) : ""
if success then
  File.open(timefile, File::CREAT|File::TRUNC|File::RDWR, 0644) do |file|
    file.puts "#{cpu.round(2)}"
  end
end

if !parallel then
	print color.call("#{cpu.round(2)} / #{time.round(2)}"), pad2, change.ljust(8), "\n"
end

sout = cstdout.read
indent = "  "

if !sout.strip.empty? then
	print "#{Time.now.strftime("%H:%M:%S")} ", color.call("==="), " #{mod}#{pad} ", "OUTPUT FOLLOWS" , "\n"
  print sout.gsub!(/^/, '  ')
end

if parallel then
	print "#{Time.now.strftime("%H:%M:%S")} ", color.call("<<<"), " #{mod}#{pad}", color.call(timing), pad2, change, ("".ljust(15 - change.strip.length)), speed, "\n"
end

exit success

rescue SignalException => e
  exit false 
end
