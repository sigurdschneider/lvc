#!/usr/bin/ruby
require 'term/ansicolor'
require 'open3'
require 'csv'

include Term::ANSIColor

@hostname=`hostname`.strip

def col(width, text) 
  return text + "".ljust(width - uncolored(text).size)
end

def rcol(width, text) 
  return "".ljust(width - uncolored(text).size) + text
end


def timefile(mod) 
	return Dir.pwd + "/" + mod.gsub(/(.*)(\/)(.*)/, '\1/.\3') + ".time"
end

if ARGV.length == 0 || ARGV[0] == "--help" then
	puts "times.sh [mod]"
	exit false
end

cmd = ARGV.join(' ')
mod = ARGV.last
timestamp = Time.now.strftime("%H:%M:%S") 
clr = lambda { |s, l, h| s >= h ? (red (s.to_s)) : (s < l ? (green (s.to_s)) : (yellow (s.to_s)))  }

num = 0
avg = 0.0
if (File.readable?(timefile(mod))) then
  CSV.foreach(timefile(mod)) do |row|
    if row[1] != nil #and row[1].strip == @hostname 
			then
			time = row[0].strip.to_f
      avg += time
			num += 1
			print "#{clr[time.round(2), 15, 75]} "
		end
  end
end
est = num > 0 ? (avg/num.to_f).round(2).to_s : "" 
print " -/- #{est}\n"
