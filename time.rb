#!/usr/bin/ruby21
require 'term/ansicolor'
require 'open3'
require 'io/console'
require 'csv'

include Term::ANSIColor

@hostname=`hostname`.strip
@width = IO.console.winsize[1]

def col(width, text)
  return text + "".ljust(width - uncolored(text).size)
end

def rcol(width, text)
  return "".ljust(width - uncolored(text).size) + text
end

def clr(s,l,h)
  return s >= h ? (green (s.to_s)) : (s < l ? (red (s.to_s)) : (yellow (s.to_s)))
end

def clr_diff(s,t)
  return s > t ? (green (s.to_s)) : ((s < (t * 0.95)) ? (red (s.to_s)) : (yellow (s.to_s)))
end

def avg(l)
  a = l.inject(0.0) { |sum, el| sum + el } / l.size
  return a.round(2)
end

def timefile(mod)
  return Dir.pwd + "/" + mod.gsub(/(.*)(\/)(.*)/, '\1/.\3') + ".time"
end

def readETA(mod)
  @times = []
  if (File.readable?(timefile(mod))) then
    CSV.foreach(timefile(mod)) do |row|
      if row[1] != nil and row[1].strip == @hostname then
	@times << row[0].strip.to_f
      end
    end
  end
  #times = times.last(1)
  est = @times.size > 0 ? @times[-1].round(2).to_s : ""
  eta = (Time.now + est.to_i).strftime("%H:%M:%S")
  return est, eta
end

def writeETA(mod, time)
  rev = `git rev-parse HEAD`
  CSV.open(timefile(mod), "ab") do |csv|
    csv << ["#{time}", "#{@hostname}", "#{Time.now.to_i}", "#{rev.strip}"]
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
  mod = ARGV.last.sub(/\.v/, "")
  modname = mod.sub("theories/", "")

  timestamp = Time.now.strftime("%H:%M:%S")

  est, eta = readETA(mod)
  eststr = "#{col(12, cyan(est))}" + (parallel ? (est == "" ? blue("ETA unavailable") : "ETA #{eta}") : "")
  print "#{timestamp} #{cyan('>>>')} #{col(35, modname)}#{eststr}#{(parallel ? "\n" : "")}"

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
  lps = (line_count / cpu).round(0)
  vosize = File.size?("#{mod}.vo").to_f
  vokps = (vosize / cpu / 1000).round(0)

  speed = success ? rcol(9, "#{line_count} L,") +
                    rcol( 9, "#{clr(lps, 15, 75)} L/s,") +
		    rcol(11, "#{clr(vokps, 15, 75)} vok/s") : ""
  if success then
    writeETA(mod, cpu)
  end

  if !parallel then
    print col(12, color[timing]), col(15, change), speed, "\n"
  end


  serrs = serr.lines[1...-4] ? serr.lines[1...-4].join : ""
  sout = cstdout.read + serrs

  if !sout.strip.empty? then
    print "#{Time.now.strftime("%H:%M:%S")} ", color["==="], " #{col(35, modname)} ", "OUTPUT FOLLOWS" , "\n"
    print sout.gsub!(/^/, '  ')
  end

  last_times = @times.last(7).map { |t| clr_diff(t.round(2), cpu.round(2))}.join(" ")

  if parallel then
    print "#{Time.now.strftime("%H:%M:%S")} ", color[success ? "<<<" : "!!!"], " #{col(35, modname)}", col(12, color[timing]), col(15, change), speed,
          ((@width > 150 && @times.size > 0) ? " #{last_times} avg #{clr_diff(avg(@times.last(7)), cpu.round(2))}" : "" ), "\n"
  end

  exit success

rescue SignalException => e
  exit false
end
