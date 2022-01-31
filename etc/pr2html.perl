#!/usr/local/bin/perl
#   Author: Robert Staerk <staerk@saul.cis.upenn.edu>
#  Created: Tue Feb  6 16:10:09 1996
#  Changes: Fri Jun 13 18:22:25 1997
# Filename: pr2html.perl
#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# Usage: pr2html.perl -o DIR DIR1/file1.pr DIR2/file2.pr ...
#
# Takes a list of LPTP proof files and converts them into 
# the following html files:
#
#     index.html file1.html file2.html ... 1.html 2.html 3.html ...
#
# The files are written into DIR.
#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# Assumptions about the syntax of LPTP proof files:
#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# :- needs_gr(FILE).
# :- needs_thm(FILE).
#
# The ":-" has to be at the beginning of the line.
# After ":-" there can be any amount of white space.
#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# :- theorem(NAME,
# FORMULA,
# DERIVATION
# ).
#
# :- lemma(NAME,
# FORMULA,
# DERIVATION
# ).
#
# :- corollary(NAME,
# FORMULA,
# DERIVATION
# ).
#
# :- axiom(NAME,
# FORMULA
# ).
#
# The ":-" has to be at the beginning of the line.
# After ":-" there can be any amount of white space.
# The "," after NAME has to be at the end of the line.
# The "," after FORMULA has to be at the end of the line.
# The ")." has to be on a separate line.
#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# :- definition_fun(NAME,ARITY,
# FORMULA,
# REFERENCES
# ).
#  
# :- definition_pred(NAME,ARITY,
# FORMULA
# ).
#
# The ":-" has to be at the beginning of the line.
# After ":-" there can be any amount of white space.
# The "," after ARITY has to be at the end of the line.
# The "," after FORMULA has to be at the end of the line.
# The ")." has to be on a separate line.
#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# /** COMMENT */
#
# In order that a comment appears in a html file it must start with "/**".
# Comments that start at the beginning of a line are printed in the
# summary files.
# Comments within proofs should not start at the beginning of a line.
#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# <TT>FORMULA</TT>
#
# Inside comments you can use "<TT>" and "</TT>" to typeset formulas.
#
# Examples:
#
#  /** In order to show <TT>succeeds member(?x,?l)</TT> we have ... */
#  /** The proof goes similar to <TT>lemma(member:termination)</TT>. */
#
#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



# Where do we have to write the html output?
if ($ARGV[0] eq '-o') {
    $html_dir = $ARGV[1];
    shift(@ARGV);
    shift(@ARGV);
} else {
    $html_dir = '.';
}

# What is the field separator for directories?
$dir_sep = '/';

# We create the signature. It is appended at the end of each html file.
@time = localtime(time);
@months = ('January',
	   'February',
	   'March',
	   'April',
	   'May',
	   'June',
	   'July',
	   'August',
	   'September',
	   'October',
	   'November',
	   'December');
$month = $months[$time[4]];
$day = $time[3];
$year = $time[5];
$year = 1900 + $year;
$date = "$month $day, $year";
$signature = "LPTP, $date";

# Default is math mode.
$math_mode = 1;

# Create the table of contents (the file index.html).
$index_html = "$html_dir${dir_sep}index.html";
open(OUT,">$index_html") || die "Cannot open $index_html\n";
print OUT "<HEAD>\n<TITLE>LPTP-Index</TITLE>\n</HEAD>\n<BODY>\n";
print OUT "<H2>LPTP: Table of Contents</H2>\n";
print OUT "<OL>\n";
foreach $file (@ARGV) {
    if ($file =~ /.pr$/) {
	$file =~ s/.pr$//;
    }
    $file =~ m|([^/]*)$|;
    $module = $1;
    print OUT "<LI><A HREF = \"$module.html\">$module</A>\n";
}
print OUT "</OL>\n";
print OUT "<HR>\n<ADDRESS>$signature</ADDRESS>\n</BODY>\n";
close(OUT);

# Create the hash table.
# 
# :- theorem(NAME,              => hash("theorem:NAME")
# :- lemma(NAME,                => hash("lemma:NAME")
# :- corollary(NAME,            => hash("corollary:NAME")
# :- axiom(NAME,                => hash("axiom:NAME")
# :- definition_fun(NAME,ARITY  => hash("definition:NAME:ARITY")
# :- definition_pred(NAME,ARITY => hash("definition:NAME:ARITY")
%hash = ();
$count = 1;
foreach $file (@ARGV) {
    unless ( $file =~ /.pr$/) {
	$file = "$file.pr";
    }
    $file =~ s|/|$dir_sep|g;
    open(IN,$file) || die "Cannot open $file\n";
    while (<IN>) {
	if ( /^:-\s*(theorem)\(([^,]*),/ || /^:-\s*(lemma)\(([^,]*),/ ||
	     /^:-\s*(corollary)\(([^,]*),/ || /^:-\s*(axiom)\(([^,]*),/ ) {
	    $hash{"$1:$2"} = $count++;
	}
	if ( /^:-\s*definition_fun\(([^,]*),([^,]*),/ ||
             /^:-\s*definition_pred\(([^,]*),([^,]*),/ ) {
	    $hash{"definition:$1:$2"} = $count++;
	}
    }
    close(IN);
}

# For each file create a table of contents of its theorems, lemmas etc.
foreach $file (@ARGV) {
    if ($file =~ /.pr$/) {
	$file =~ s/.pr$//;
    }
    $file =~ m|([^/]*)$|;
    $module = $1;
    $file =~ s|/|$dir_sep|g;
    $file_pr = "$file.pr";
    $file_html = "$html_dir$dir_sep$module.html";
    open(IN,$file_pr) || die "Cannot open $file_pr\n";
    open(OUT,">$file_html") || die "Cannot open $file_html\n";
    print OUT "<HEAD>\n<TITLE>$module</TITLE>\n</HEAD>\n<BODY>\n";
    print OUT "[<A HREF = \"index.html\">Index</A>]\n";
    print OUT "<H2>Module: $module</H2>\n<PRE>\n";
    while (<IN>) {
        &needs_gr;
	&needs_thm;
	&fact;
	&definition;
	&comment;
    }
    print OUT "</PRE>\n[<A HREF = \"index.html\">Index</A>]\n";
    print OUT "<HR>\n<ADDRESS>$signature</ADDRESS>\n</BODY>\n";
    close(OUT);
    close(IN);
}

# Split each file into single theorems.
foreach $file (@ARGV) {
    if ($file =~ /.pr$/) {
	$file =~ s/.pr$//;
    }
    $file =~ m|([^/]*)$|;
    $module = $1;
    $file =~ s|/|$dir_sep|g;
    $file_pr = "$file.pr";
    open(IN,$file_pr) || die "Cannot open $file_pr\n";
    while (<IN>) {
	&new_fact;
	&new_definition;
	if ($out) {
	    print OUT &typeset($_);
        }
        &close_module;
    }
    close(IN);
}

sub needs_gr {
    if ( /^:-\s*needs_gr\((.*)\)\./ ) {
	$1 =~ m|([^/]*)$|;
	$needs = $1;
	print OUT "<B>Needs Prolog code of </B>";
	print OUT "<A HREF = \"$needs-code.html\">$needs</A><BR>\n";
    }
}

sub needs_thm {
    if ( /^:-\s*needs_thm\((.*)\)\./ ) {
	$1 =~ m|([^/]*)$|;
	$needs = $1;
	print OUT "<B>Needs theorems of </B>";
	print OUT "<A HREF = \"$needs.html\">$needs</A><BR>\n";
    }
}

sub fact {
    if ( /^:-\s*(theorem)/ || /^:-\s*(lemma)/ ||
	 /^:-\s*(corollary)/ || /^:-\s*(axiom)/ ) {
	$kind = $1;
	$' =~ /^\(([^,]*),$/;
	$name = $1;
	$module_nr = $hash{"$kind:$name"};
	print OUT "\n<B><A HREF =\"$module_nr.html\">\u$kind</A></B>";
	print OUT "(<I><A NAME = \"$module_nr\">$name</A></I>)\n";
	while (<IN>) {
	    if ( /,$/ ) {
		print OUT &typeset($`) . ".\n";
		last;
	    } elsif ( /^\)\.$/ ) {
		last;
	    } else {
		print OUT &typeset($_);
	    }
	}
    }
}

sub definition {
    if ( /^:-\s*definition_fun\(([^,]*),([^,]*),/ ||
         /^:-\s*definition_pred\(([^,]*),([^,]*),/ ) {
	$module_nr = $hash{"definition:$1:$2"};
	print OUT "\n<B><A HREF =\"$module_nr.html\">";
	print OUT "Definition</A></B>";
	print OUT "(<I><A NAME = \"$module_nr\">$1/$2</A></I>)\n";
	while (<IN>) {
	    if ( /,$/ ) {
		print OUT &typeset($`) . ".\n";
		last;
	    } elsif ( /\)\.$/ ) {
		last;
	    } else {
		print OUT &typeset($_);
	    }
	}
    }
}

sub comment {
    if ( m@^/\*\*\s*@ ) {
	print OUT "</PRE>\n";
	$_ = $';
	$math_mode = 0;
	while ($_) {
	    if ( m@\*/@ ) {
		print OUT &typeset($`) . "\n<PRE>";
		$_ = <IN>;
		last;
	    } else {
		print OUT &typeset($_);
		$_ = <IN>;
	    }
	}
	$math_mode = 1;
    }
}

sub new_fact {
    if ( /^:-\s*(theorem)/ || /^:-\s*(lemma)/ ||
	 /^:-\s*(corollary)/ || /^:-\s*(axiom)/ ) {
	$kind = $1;
	$' =~ /^\(([^,]*),$/;
	$module_nr = $hash{"$kind:$1"};
	$out = 1;
	$file_out = "$html_dir$dir_sep$module_nr.html";
	open(OUT,">$file_out") || die "Cannot open $file_out\n";
	print OUT "<HEAD>\n<TITLE>$1</TITLE>\n</HEAD>\n<BODY>\n<PRE>\n";
	print OUT "<B>\u$kind</B>(<I>$1</I>,\n";
	next;
    }
}

sub new_definition {
    if ( /^:-\s*(definition_pred)/ || /^:-\s*(definition_fun)/ ) {
    	$kind = $1;
    	$' =~ /^\(([^,]*),([^,]*),$/;
    	$module_nr = $hash{"definition:$1:$2"};
    	$out = 1;
	$file_out = "$html_dir$dir_sep$module_nr.html";
	open(OUT,">$file_out") || die "Cannot open $file_out\n";
	print OUT "<HEAD>\n<TITLE>$1/$2</TITLE>\n</HEAD>\n<BODY>\n<PRE>\n";
	print OUT "<B>\u$kind</B>(<I>$1,$2,</I>\n";
	next;
    }
}

sub close_module {
    if ( $out && /\)\.$/ ) {
	print OUT "\n[<B><A HREF = \"$module.html#$module_nr\">Module</A></B> ";
	print OUT "<I>$module</I>]";
	print OUT "</PRE>\n<HR>\n<ADDRESS>$signature</ADDRESS>\n</BODY>\n";
	close(OUT);
	$out = 0;
    }   
}

sub typeset {
    local($text) = $_[0];
    $result = '';
    while ($text) {
	if ($math_mode) {	# We are in math mode.
	    if ($text =~ m@/\*\*@) {
		$result .= &substitute($`) . '<I>/**';
		$text = $';
		$math_mode = 0;
	    } elsif ($text =~ m@</TT>@) {
		$result .= &substitute($`) . '</TT>';
		$text = $';
		$math_mode = 0;
	    } else {
		$result .= &substitute($text);
		$text = '';
	    }
	} else {		# We are in text mode.
	    if ($text =~ m@\*/@) {
		$result .= $` . '*/</I>';
		$text = $';
		$math_mode = 1;
	    } elsif ($text =~ m@<TT>@) {
		$result .= $` . '<TT>';
		$text = $';
		$math_mode = 1;
	    } else {
		$result .= $text;
		$text = '';
	    }
	}
    }
    $result;
}

sub substitute {
    local($s) = $_[0];

    $s =~ s@succeeds @<B>S</B> @g;
    $s =~ s@succeeds\(@<B>S</B>\(@g;
    $s =~ s@fails @<B>F</B> @g;
    $s =~ s@fails\(@<B>F</B>\(@g;
    $s =~ s@terminates @<B>T</B> @g;
    $s =~ s@terminates\(@<B>T</B>\(@g;
    $s =~ s@def @<B>D</B> @g;
    $s =~ s@def\(@<B>D</B>\(@g;

    $s =~ s@induction\(@<B>induction</B>\(@g;
    $s =~ s@step\(@<B>step</B>\(@g;
    $s =~ s@assume\(@<B>assume</B>\(@g;
    $s =~ s@cases\(@<B>cases</B>\(@g;
    $s =~ s@case\(@<B>case</B>\(@g;
    $s =~ s@exist\(@<B>exist</B>\(@g;
    $s =~ s@contra\(@<B>contra</B>\(@g;
    $s =~ s@indirect\(@<B>indirect</B>\(@g;

    $s =~ s@\?([a-zA-Z0-9_]*)@<I>\?$1</I>@g;
    $s =~ s@all \[([a-zA-Z0-9_,]*)\]@all \[<I>$1</I>\]@g;
    $s =~ s@all ([a-zA-Z0-9_]*)@all <I>$1</I>@g;
    $s =~ s@ex \[([a-zA-Z0-9_,]*)\]@ex \[<I>$1</I>\]@g;
    $s =~ s@ex ([a-zA-Z0-9_]*)@ex <I>$1</I>@g;

    $s =~ s@theorem\(([^)]*)\)@<I><A HREF = "$hash{"theorem:".$1}.html">Theorem</A>\($1\)</I>@g;
    $s =~ s@lemma\(([^)]*)\)@<I><A HREF = "$hash{"lemma:".$1}.html">Lemma</A>\($1\)</I>@g;
    $s =~ s@corollary\(([^)]*)\)@<I><A HREF = "$hash{"corollary:".$1}.html">Corollary</A>\($1\)</I>@g;
    $s =~ s@axiom\(([^)]*)\)@<I><A HREF = "$hash{"axiom:".$1}.html">Axiom</A>\($1\)</I>@g;
    
    if ( m@uniqueness\(([^,]*),([^,]*)\)@ ) {
    	$nr = $hash{"definition:$1:$2"};
    	$s =~ s@uniqueness\(([^,]*),([^,]*)\)@<I><A HREF = "$nr.html">uniqueness</A>\($1,$2\)</I>@;
    }

    if ( m@existence\(([^,]*),([^,]*)\)@ ) {
    	$nr = $hash{"definition:$1:$2"};
    	$s =~ s@existence\(([^,]*),([^,]*)\)@<I><A HREF = "$nr.html">existence</A>\($1,$2\)</I>@;
    }

    if ( m@introduction\(([^,]*),([^,]*)\)@ ) {
    	$nr = $hash{"definition:$1:$2"};
    	$s =~ s@introduction\(([^,]*),([^,]*)\)@<I><A HREF = "$nr.html">introduction</A>\($1,$2\)</I>@;
    }

    if ( m@elimination\(([^,]*),([^,]*)\)@ ) {
    	$nr = $hash{"definition:$1:$2"};
    	$s =~ s@elimination\(([^,]*),([^,]*)\)@<I><A HREF = "$nr.html">elimination</A>\($1,$2\)</I>@;
    }

    $s
}

1;
