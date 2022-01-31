#   Author: Robert Staerk <staerk@rz.mathematik.uni-muenchen.de>
#  Created: Tue Jun 14 18:21:39 1994
# Updated: Wed Jul 21 17:01:11 1999
# Filename: Makefile

SOURCES =	op.pl \
		system.pl \
		obj.pl \
		e2i.pl \
		i2e.pl \
		pr.pl \
		cmp.pl \
		bi.pl \
		def.pl \
		dep.pl \
		ind.pl \
		eq.pl \
		mgu.pl \
		tac.pl \
		ai.pl \
		ctl.pl \
		prt.pl \
		tex.pl \
		lst.pl \
		io.pl \
		gnd.pl \
		alias.pl

RM =		/bin/rm -f
MV =		/bin/mv -f
CP = 		/bin/cp -f

# Create the file `pred.txt' containing all `%%d' definitions.
def: $(SOURCES)
	grep -h '%%d' $(SOURCES) | sort > /tmp/pred.txt
	sed -e 's/%%d/%%/g' /tmp/pred.txt > pred.txt
	$(RM) /tmp/pred.txt

# Collect all comments starting with `%%c' in the file `doc.txt'.
doc: $(SOURCES) def
	grep -h '%%c' $(SOURCES) > /tmp/doc.txt
	sed -e 's/%%c/%%/g' /tmp/doc.txt > doc.txt
	cat pred.txt >> doc.txt
	$(RM) /tmp/doc.txt

# Create file `allg.txt' from `all.pl'
allg:	all.pl
	sed "s/:-//g" all.pl > allg.pl

# Create file `initg.pl' from `init.pl'
initg: init.pl
	sed "s/consult/include/" init.pl > initg.pl

# Conncatenate all Prolog source files into one big file `lptp.pl'.
# Don't forget to change `io__lptp_home' in `system.pl'.
lptp: $(SOURCES) 
	cat $(SOURCES) > lptp.pl

# Compile LPTP (SICStus Prolog)
sicstus: lptp
	echo "[op]. prolog_flag(compiling,_,fastcode). fcompile(lptp)."\
	| sicstus

# Compile LPTP for debugging (SICStus Prolog)
profile: $(SOURCES)
	echo "[op]. prolog_flag(compiling,_,profiledcode). fcompile(lptp)."\
	| sicstus

# Compile LPTP for GNU Prolog
gprolog: lptp
	gplc --global-size 16384 -o lptp lptp.pl

clean:
	$(RM) *~ *mist mist* prolog/*~ *.ql lptp.pl lptp.qlf \
	pred.txt doc.txt lptp

