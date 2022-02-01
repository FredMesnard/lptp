#!/usr/local/bin/perl
#   Author: Robert Staerk <staerk@saul.cis.upenn.edu>
#  Created: Tue Feb  6 16:10:09 1996
# Filename: pl2html.perl
# Abstract: This script takes a list of Prolog source code files
#
#     file1.pl file2.pl ...
#
# and converts them into files
#
#     file1-code.html file2-code.thml ...
#
# Options:
#
#  -o DIRECTORY:  the output files are written into DIRECTORY
#

# Where to write the html output?
if ($ARGV[0] eq '-o') {
    $html_dir = $ARGV[1];
    shift(@ARGV);
    shift(@ARGV);
} else {
    $html_dir = '.';
}

# What is the field separator for directories?
$dir_sep = '/';

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

$lib_html = "$html_dir${dir_sep}lib.html";

# Create the Prolog source code files
foreach $file (@ARGV) {
    if ($file =~ /.pl$/) {
	$file =~ s/.pl$//;
    }
    $file =~ m@([^/]*)$@;
    $module = $1;
    $file =~ s@/@$dir_sep@g;
    $file_pl = "$file.pl";
    $file_html = "$html_dir$dir_sep$module-code.html";
    open(IN,$file_pl) || die "Cannot open $file_pl\n";
    open(OUT,">$file_html") || die "Cannot open $file_html\n";
    print OUT "<HEAD>\n<TITLE>$module</TITLE>\n</HEAD>\n<BODY>\n";
    print OUT "<H2>Prolog predicates for module $module</H2>\n<PRE>\n";
    while (<IN>) {
	print OUT $_;
    }
    print OUT "</PRE>\n<HR>\n<ADDRESS>$signature</ADDRESS>\n</BODY>\n";
    close(OUT);
    close(IN);
}

1;
