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

$asstotal = ARGV[0].to_i
print "Assuming #{$asstotal} total LoC for % calculation."

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
    r = Metrics.new()
    r.increment(self)
    r.increment(o)
    return r
  end

  def increment(o)
    @tloc += o.tloc
    @sloc += o.sloc
    @ploc += o.ploc
    @count += o.count
    @lcnt += o.lcnt
    @dcnt += o.dcnt
    @tactics += o.tactics
    @fixpoints += o.fixpoints
    return self
  end

  def write_tex(file, name)
    k = "\\#{name.gsub(/\s+/,"")}"
    file.write("\\newcommand{#{k}}{#{@tloc}}\n");
    file.write("\\newcommand{#{k}Spec}{#{@sloc}}\n");
    file.write("\\newcommand{#{k}Proof}{#{@ploc}}\n");
    file.write("\\newcommand{#{k}Files}{#{@count}}\n");
    file.write("\\newcommand{#{k}Lemmas}{#{@lcnt}}\n");
    file.write("\\newcommand{#{k}Definitions}{#{@dcnt}}\n");
    file.write("\\newcommand{#{k}Tactics}{#{@tactics}}\n");
    file.write("\\newcommand{#{k}Fixpoints}{#{@fixpoints}}\n");
		file.write("\\newcommand{#{k}Percentage}{#{(@tloc.to_f*100/$asstotal.to_f).round(0)}}\n");
    l = "\\mkSep#{k}"
    file.write("\\newcommand{#{k}Data}{#{l}Spec&#{l}Proof&#{l}Lemmas&#{l}Definitions&#{l}Tactics&#{l}Percentage}\n");
  end

end

def loc(paths, exts=Set.new([".v"]), onlynew=false)
  mt = Metrics.new()
  paths.each { |path|
    Find.find(*Dir.glob("#{path}")) do |path|
      if exts.include?(File.extname(path)) then
        if @acc[path] == 0 or not onlynew then
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
#          print "   #{path}\n", mt.to_s,"\n"
          @acc[path] += 1
        end
      end
    end
  }
  return mt
end

@texcmds = File.open("loc.tex", 'w')

def comp(total, name, paths, exts=Set.new([".v"]), silent=false, onlynew=false)
  mt = loc(paths, exts, onlynew)
  total.increment(mt)
  if not silent then print mt.to_s, " ", name, "\n" end
  mt.write_tex(@texcmds, name)
end

ext = Metrics.new()
comp(ext, "paco", ["paco/*"], [".v", ".ml4"], true)
comp(ext, "containers", ["ContainersPlugin/"], [".v", ".ml4"], true)

fund = Metrics.new()
comp(fund, "Sets and Maps", ["theories/Constr"])
comp(fund, "Utilities and Tactics", ["theories/Infra"])

il = Metrics.new()
comp(il, "Semantics", ["theories/IL", "theories/Isa"])
comp(il, "Equivalence", ["theories/Equiv"])
comp(il, "Coherence", ["theories/Coherence/Coherence.v", "theories/Coherence/Restrict.v", "theories/Coherence/Coherence_*.v"])
comp(il, "Alpha Equivalence", ["theories/Alpha"])

regalloc = Metrics.new()
spilling = Metrics.new()
comp(regalloc, "Register Assignment", ["theories/Coherence/Allocation*", "theories/RegAssign.v", "theories/RenameApartToPart.v"])
comp(spilling, "TVRepair", ["theories/Spilling/Repair*", "theories/Spilling/Pick*", "theories/Spilling/LiveMin*", "theories/Spilling/SpillMaxKill*",
                            "theories/Spilling/RLive*", "theories/Spilling/RegLive*"])
comp(spilling, "ReconstrLive", ["theories/Spilling/Reconstr*"])
comp(spilling, "Spilling", ["theories/Spilling"], Set.new([".v"]), false, true)
regalloc += spilling

@total = Metrics.new()
comp(@total, "Analyses", ["theories/Analysis", "theories/Liveness", "theories/Reachability"])
comp(@total, "Value Optimizations", ["theories/ValueOpts"])
comp(@total, "Dead Code Elimination", ["theories/DeadCodeElimination"])
comp(@total, "Lowering", ["theories/Lowering"])
comp(@total, "SMT Translation Validation", ["theories/TransVal"])
comp(@total, "SSA Construction", ["theories/Coherence/AddParam.v", "theories/Coherence/Delocation*", "theories/Coherence/Invariance.v",
                                  "theories/Coherence/AddParams.v", "theories/Coherence/AddAdd.v"])
comp(@total, "OCaml Integration", ["compiler/*.ml", "compiler/*.mll", "compiler/*.v", "compiler/*.mly", "theories/Compiler.v"], [".ml", ".v", ".mll", ",mly"])
comp(@total, "Coq Plugin", ["src/*.ml4"], [".ml4"])

@total += fund + il + regalloc
if ($asstotal != @total) then
	print "!!! Warning, assumed total LoC different from total Loc: #{@total.to_s}\n\n"
end
print @total.to_s, " in LVC in total\n"
@total.write_tex(@texcmds, "Total")
print ext.to_s, " in external dependencies\n"
ext.write_tex(@texcmds, "External")
fund.write_tex(@texcmds, "Foundations")
il.write_tex(@texcmds, "IntermediateLanguage")
regalloc.write_tex(@texcmds, "RegisterAllocation")
spilling.write_tex(@texcmds, "SpillingAll")

Find.find("theories/") do |path|
  if File.extname(path) == ".v" then
    if @acc[path] == 0 then
      print "Unaccounted #{path}\n"
    elsif @acc[path] > 1 then
      print "Multiacc #{@acc[path]} #{path}\n"
    end
  end
end
