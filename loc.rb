#!/usr/bin/ruby
require 'term/ansicolor'
require 'open3'
require 'io/console'
require 'csv'
require 'find'
require 'set'

include Term::ANSIColor

@width = IO.console.winsize[1]
@acc = Hash.new(0)
@total = Hash.new(0)

def loc(paths, exts=Set.new([".v"]))
  tloc = 0
  count = 0
	paths.each { |path|
    Find.find(*Dir.glob("#{path}")) do |path|
	    if exts.include?(File.extname(path)) then
		    loc, _ = `wc -l #{path}`.strip.split(" ")
				#print path, "\n"
  	    tloc += loc.to_i
  	    count += 1
				@acc[path] += 1
    	end
    end
	}
	return tloc, count
end

def rcol(width, text)
	  return "".ljust(width - uncolored(text).size) + text
end

def str(loc, count)
	return "#{rcol(6, "#{loc}")} loc in #{rcol(3, "#{count}")} files"
end

@texcmds = File.open("loc.tex", 'w')

def comp(name, paths, exts=Set.new([".v"]))
  l, c = loc(paths, exts)
	@total["loc"] += l
	@total["count"] += c
  print str(l,c), " ", name, "\n"
  @texcmds.write("\\newcommand{\\#{name.gsub(/\s+/,"")}}{#{l}}\n");
end

comp("External Dependecies", ["paco/*", "ContainersPlugin/"], [".v", ".ml4"])
@total = Hash.new(0)
comp("Libraries and Tactics", ["theories/Constr", "theories/Infra"])
comp("Semantics", ["theories/IL", "theories/Isa"])
comp("Equivalence", ["theories/Equiv"])
comp("Analyses", ["theories/Analysis", "theories/Liveness", "theories/Reachability"])
comp("Value Optimizations", ["theories/ValueOpts"])
comp("Dead Code Elimination", ["theories/DVE.v", "theories/UCE.v", "theories/DCVE.v", "theories/DCE.v"])
comp("Register Assignment", ["theories/Coherence/Allocation*"])
comp("Spilling", ["theories/Spilling"])
comp("Lowering", ["theories/Lowering"])
comp("Alpha Equivalence", ["theories/Alpha"])
comp("SMT Translation Validation", ["theories/TransVal"])
comp("SSA Construction", ["theories/Coherence/Coherence.v", "theories/Coherence/Delocation*", "theories/Coherence/Invariance.v",
                          "theories/Coherence/Restrict.v"])
comp("OCaml Integration", ["compiler/*.ml", "compiler/*.mll", "compiler/*.v", "compiler/*.mly"], [".ml", ".v", ".mll", ",mly"])
comp("Coq Plugin", ["src/*.ml4"], [".ml4"])

print @total["loc"],  " loc in ", @total["count"], " files in total\n"

Find.find("theories/") do |path|
  if File.extname(path) == ".v" then
		if @acc[path] == 0 then
			print "Unaccounted #{path}\n"
		elsif @acc[path] > 1 then
			print "Multiacc #{@acc[path]} #{path}\n"
		end
	end
end
