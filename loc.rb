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

def rcol(width, text)
  return "".ljust(width - uncolored(text).size) + text
end

def rcoli(width, text)
  return rcol(width, text.to_s)
end

class Metrics
  attr_accessor :tloc
  attr_accessor :sloc
  attr_accessor :ploc
  attr_accessor :count
  attr_accessor :lcnt
  attr_accessor :dcnt
  attr_accessor :tactics
  attr_accessor :fixpoints

  def initialize(tloc=0, sloc=0, ploc=0, count=0, lcnt=0, dcnt=0, tactics=0, fixpoints=0)
    @tloc = tloc
    @sloc = sloc
    @ploc = ploc
    @count = count
    @lcnt = lcnt
    @dcnt = dcnt
    @tactics = tactics
    @fixpoints = fixpoints
  end

  def to_s
    return "#{rcoli(6, @tloc)} loc (#{rcoli(5,@sloc)} spec, #{rcoli(5,@ploc)} proof) for #{rcoli(4,@lcnt)} lemmas and #{rcoli(4,@dcnt)} definitions (#{rcoli(4,@fixpoints)} of those fixpoints) and #{rcoli(3,@tactics)} tactics in #{rcoli(3, @count)} files"
  end

  def +(o)
    return Metrics.new(@tloc+o.tloc, @sloc+o.sloc, @ploc+o.ploc, @count+o.count, @lcnt+o.lcnt, @dcnt+o.dcnt, @tactics+o.tactics, @fixpoints+o.fixpoints)
  end

  def write_tex(file, name)
    file.write("\\newcommand{\\#{name.gsub(/\s+/,"")}}{#{@tloc}}\n");
    file.write("\\newcommand{\\#{name.gsub(/\s+/,"")}Spec}{#{@sloc}}\n");
    file.write("\\newcommand{\\#{name.gsub(/\s+/,"")}Proof}{#{@ploc}}\n");
    file.write("\\newcommand{\\#{name.gsub(/\s+/,"")}Files}{#{@count}}\n");
    file.write("\\newcommand{\\#{name.gsub(/\s+/,"")}Lemmas}{#{@lcnt}}\n");
    file.write("\\newcommand{\\#{name.gsub(/\s+/,"")}Definitions}{#{@dcnt}}\n");
    file.write("\\newcommand{\\#{name.gsub(/\s+/,"")}Tactics}{#{@tactics}}\n");
    file.write("\\newcommand{\\#{name.gsub(/\s+/,"")}Fixpoints}{#{@fixpoints}}\n");
  end

end

@total = Metrics.new()

def loc(paths, exts=Set.new([".v"]))
  mt = Metrics.new()
  paths.each { |path|
    Find.find(*Dir.glob("#{path}")) do |path|
      if exts.include?(File.extname(path)) then
        loc, _ = `wc -l #{path}`.strip.split(" ")
        coqspec = `coqwc -s #{path}`
        coqproof = `coqwc -r #{path}`
        lemmas = `grep -e 'Lemma\\|Theorem\\|Corollary\\|Instance' #{path} | wc -l`
        defs = `grep -e 'Definition\\|Inductive\\|Record\\|Class\\|Fixpoint' #{path} | wc -l`
        fixpoints = `grep -e 'Fixpoint' #{path} | wc -l`
        tactics = `grep -e 'Smpl\\|Ltac\\|Tactic' #{path} | wc -l`
        if File.extname(path) == ".v" then
          mt.tloc += coqspec.to_i + coqproof.to_i
          mt.sloc += coqspec.to_i
          mt.ploc += coqproof.to_i
          mt.lcnt += lemmas.to_i
          mt.dcnt += defs.to_i
          mt.tactics += tactics.to_i
          mt.fixpoints += fixpoints.to_i
        else
          mt.tloc += loc.to_i
        end
        mt.count += 1
        @acc[path] += 1
      end
    end
  }
  return mt
end

@texcmds = File.open("loc.tex", 'w')

def comp(name, paths, exts=Set.new([".v"]), silent=false)
  mt = loc(paths, exts)
  @total += mt
  if not silent then print mt.to_s, " ", name, "\n" end
  mt.write_tex(@texcmds, name)
end

comp("paco", ["paco/*"], [".v", ".ml4"], true)
comp("containers", ["ContainersPlugin/"], [".v", ".ml4"], true)
ext=@total
@total = Metrics.new()
comp("Sets and Maps", ["theories/Constr"])
comp("Utilities and Tactics", ["theories/Infra"])
comp("Semantics", ["theories/IL", "theories/Isa"])
comp("Equivalence", ["theories/Equiv"])
comp("Coherence", ["theories/Coherence/Coherence.v", "theories/Coherence/Restrict.v", "theories/Coherence/Coherence_*.v"])
comp("Analyses", ["theories/Analysis", "theories/Liveness", "theories/Reachability"])
comp("Value Optimizations", ["theories/ValueOpts"])
comp("Dead Code Elimination", ["theories/DVE.v", "theories/UCE.v", "theories/DCVE.v", "theories/DCE.v"])
comp("Register Assignment", ["theories/Coherence/Allocation*", "theories/RegAssign.v", "theories/RenameApartToPart.v"])
comp("Spilling", ["theories/Spilling"])
comp("Lowering", ["theories/Lowering"])
comp("Alpha Equivalence", ["theories/Alpha"])
comp("SMT Translation Validation", ["theories/TransVal"])
comp("SSA Construction", ["theories/Coherence/AddParam.v", "theories/Coherence/Delocation*", "theories/Coherence/Invariance.v",
                          "theories/Coherence/AddParams.v", "theories/Coherence/AddAdd.v"])
comp("OCaml Integration", ["compiler/*.ml", "compiler/*.mll", "compiler/*.v", "compiler/*.mly", "theories/Compiler.v"], [".ml", ".v", ".mll", ",mly"])
comp("Coq Plugin", ["src/*.ml4"], [".ml4"])

print @total.to_s, " in LVC in total\n"
print ext.to_s, " in external dependencies\n"

Find.find("theories/") do |path|
  if File.extname(path) == ".v" then
    if @acc[path] == 0 then
      print "Unaccounted #{path}\n"
    elsif @acc[path] > 1 then
      print "Multiacc #{@acc[path]} #{path}\n"
    end
  end
end
