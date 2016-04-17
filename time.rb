#!/usr/bin/ruby21
require 'term/ansicolor'
require 'open3'

include Term::ANSIColor

def col(width, text) 
  return text + "".ljust(width - uncolored(text).length)
end

def timefile(mod) 
	return mod.gsub(/(.*)(\/)(.*)/, '\1/.\3') + ".time"
end

def readETA(mod)
	est = File.readable?(timefile(mod)) ? File.read(timefile(mod)).strip : ""
  eta = (Time.now + est.to_i).strftime("%H:%M:%S")
  return est, eta 
end

def writeETA(mod, time)
  File.open(timefile(mod), File::CREAT|File::TRUNC|File::RDWR, 0644) do |file|
    file.puts "#{time.round(2)}"
  end
end	

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
timestamp = Time.now.strftime("%H:%M:%S") 

est, eta = readETA(mod) 
eststr = "#{col(12, cyan(est))}" + (parallel ? (est == "" ? blue("ETA unavailable") : "ETA #{eta}") : "")
print "#{timestamp} #{cyan('>>>')} #{col(30, mod)}#{eststr}#{(parallel ? "\n" : "")}"

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
timing = "#{cpu.round(2)}"
changesec = (time - est.to_f)
changesecstr = sprintf("%+.2f (%+.1f%%)", changesec, (100*changesec/est.to_f)) 
change = est == "" ? blue("n/a") : (changesec <= 0 ? green(changesecstr) : red(changesecstr))
line_count = `wc -l "#{mod}.v"`.strip.split(' ')[0].to_i
spl = (line_count / cpu).round(0)
speed = success ? ("#{line_count} L,".rjust(9) + "#{spl} L/s".rjust(8)) : ""
if success then
	writeETA(mod, cpu)
end

if !parallel then
	print col(12, color[timing]), col(15, change), speed, "\n"
end

sout = cstdout.read

if !sout.strip.empty? then
	print "#{Time.now.strftime("%H:%M:%S")} ", color["==="], " #{col(30, mod)} ", "OUTPUT FOLLOWS" , "\n"
  print sout.gsub!(/^/, '  ')
end

if parallel then
	print "#{Time.now.strftime("%H:%M:%S")} ", color["<<<"], " #{col(30, mod)}", col(12, color[timing]), col(15, change), speed, "\n"
end

exit success

rescue SignalException => e
  exit false 
end
