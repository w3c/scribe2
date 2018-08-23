#!/usr/bin/perl
#
# Converts an IRC log to formatted minutes in HTML.
#
# See scribe2doc.html for the manual.
# This is a rewrite of David Booth's scribe.perl
#
# TODO: Omit failed s/// commands? (But maybe they failed on purpose
# and should not be removed?)
#
# TODO: option --inputFormat to select the format, rather than try
# each parser in turn.
#
# TODO: Allow (and ignore) the unused options of old scribe.perl?
#
# TODO: Add a command ('oops'? 'undo'? 'ignore'? u///g?) to remove an
# incorrect s///g, because s|s/.../.../g|| doesn't remove it.
#
# TODO: Warn about unrecognized or impossible dates after "Date: ..."
#
# TODO: A streaming mode (using --inputFormat) that formats each line
# as soon as it is read? (s/// and i//// will not work. ScribeNick is
# not retroactive. Broken lines, as in Mirc logs, are not recombined.)
#
# TODO: Add a "next meeting" command that adds a link at the top of
# the minutes. Like "previous meeting", it could accept a URL. But it
# could also accept a date or a period: "next meeting: 7 Aug", "next
# meeting: 2 weeks".
#
# TODO: Format trackbot's output specially: created an action/issue,
# info about an action/issue, etc.
#
# Copyright © 2017-2018 World Wide Web Consortium, (Massachusetts Institute
# of Technology, European Research Consortium for Informatics and
# Mathematics, Keio University, Beihang). All Rights Reserved. This
# work is distributed under the W3C® Software License[1] in the hope
# that it will be useful, but WITHOUT ANY WARRANTY; without even the
# implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
# PURPOSE.
#
# [1] http://www.w3.org/Consortium/Legal/2015/copyright-software-and-document
# or see the file COPYING included in this distribution.
#
# Created: 3 Feb 2017
# Author: Bert Bos <bert@w3.org>


# Conversion proceeds in four steps:
#
# 1) Various parsers are tried to normalize the lines of the input
# into an array of records (see below for the structure of the
# records).
#
# 2) Process "s/old/new/" and "i/where/what/" commands.
#
# 3) Each record is interpreted, looking for topics, present & regrets,
# actions, resolutions, scribes, statements or summaries minuted by
# the scribes, and remarks by other people on IRC. Each record is
# modified and classified accordingly.
#
# 4) The array of records is converted to an HTML fragment and that
# fragment, together with the collected topics, actions, etc. are
# inserted into an HTML template and printed.
#
# Each record has four fields: {type, speaker, id, text}
# If type is 'i' (irc), <speaker> is the person who typed <text>.
# If type is 's' (scribe), <speaker> is the person who said <text> on the phone.
# If type is 'd' (description) <text> is a summary by the scribe.
# If type is 't' (topic), <text> is the title for a new topic.
# If type is 'a' (action), <text> is an action and <id> is a unique ID.
# If type is 'r' (resolution), <text> is a resolution and <id> is a unique ID.
# if type is 'u' (issue), <speaker> is a #, <text> is an issue, <id> a unique ID.
# If type is 'c' (change), the record is a s/// or i/// not (yet) successful
# If type is 'o' (omit), the record is to be ignored.
# If type is 'n' (named anchor), the record is a target anchor.

use strict;
use warnings;
use Getopt::Long qw(GetOptionsFromString :config auto_version auto_help);
use Pod::Usage;
use 5.012;			# We use "each @ARRAY"
use locale;			# Sort using current locale

my $urlpat= '(?:[a-z]+://|mailto:[^\s<@]+\@|geo:[0-9.]|urn:[a-z0-9-]+:)[^\s<]+';

# Command line options:
my $is_team = 0;		# If 1, use team style
my $is_member = 0;		# If 1, use member style
my $is_fancy = 0;		# If 1, use the fancy style
my $embed_diagnostics = 0;	# If 1, put warnings in the HTML, not on STDERR
my $implicitcont = 0;		# If 1, lines without '…' are continuations, too
my $spacecont = 0;		# If 1, initial space may replace '…'
my $keeplines = 1;		# If 1, put <br> between continuation lines
my $final = 0;                  # If 1, don't include "DRAFT" warning in minutes
my $scribenick;			# Nick of the current scribe in lowercase
my $dash_topics = 0;		# If 1, "--" means the next line is a topic
my $use_zakim = 1;		# If 1, treat conversations with Zakim specially
my $scribeonly = 0;		# If 1, omit IRC comments by others
my $emphasis = 0;		# If 1, _xxx_, *xxx* and /xxx/ highlight things 
my $old_style = 0;		# If 1, use the old (pre-2017) style sheets
my $url_display = 'break';	# How to display in-your-face URLs
my $logo;			# undef = W3C logo; string = HTML fragment


# Each parser takes a reference to an array of text lines (newlines
# included) and a reference to an array of records. It returns 0
# (failed to parse) or 1 (success) and it appends successfully parsed
# lines to the array of records, with {type} set to 'i' and {speaker}
# and {text} set to the text and the nick of the person who typed that
# text. It sets {id} to the empty string. It should not try to parse
# the text futher for actions, resolutions, etc.
#
# IRC messages ("X joined channel Y"), time stamps, private messages,
# and off-the-record text ("/me waves") are omitted.
#
# The parsers are tried in turn until one succeeds, so their order is
# important. E.g., the Plain_Text_Format should probably be towards
# the end.

my @parsers = (\&RRSAgent_text_format, \&Bip_Format, \&Mirc_Text_Format,
	       \&Yahoo_IM_Format, \&Bert_IRSSI_Format, \&Plain_Text_Format);


# RRSAgent_text_format -- parse an IRC log as generated by RRSAgent
sub RRSAgent_text_format($$)
{
  my ($lines_ref, $records_ref) = @_;

  foreach (@$lines_ref) {
    if (/^(?:\d\d:\d\d:\d\d )?<([^ >]+)> \1 has (joined|left) /) {
      # Ignore lines like "<jfm> jfm has joined #foo"
    } elsif (/^(?:\d\d:\d\d:\d\d )?<([^ >]+)> (.*)/) {
      push(@$records_ref, {type=>'i', id=>'', speaker=>$1, text=>$2});
    } elsif (/^\s*$/) {
      # Ignore empty lines
    } else {
      return 0;			# Unknown format, give up
    }
  }
  return 1;
}


# Bip_Format -- parse an IRC log generated by bip
sub Bip_Format($$)
{
  my ($lines_ref, $records_ref) = @_;

  foreach (@$lines_ref) {
    if (/^\d\d-\d\d-\d{4} \d\d:\d\d:\d\d -!- /) {
      # IRC server message, ignore
    } elsif (/^\d\d-\d\d-\d{4} \d\d:\d\d:\d\d [<>] \* /) {
      # /me message, ignore
    } elsif (/^\d\d-\d\d-\d{4} \d\d:\d\d:\d\d < ([^ !:]+)![^ :]+: (.*)$/) {
      push(@$records_ref, {type=>'i', id=>'', speaker=>$1, text=>$2});
    } elsif (/^\d\d-\d\d-\d{4} \d\d:\d\d:\d\d > ([^ :]+): (.*)$/) {
      push(@$records_ref, {type=>'i', id=>'', speaker=>$1, text=>$2});
    } elsif (/^\s*$/) {
      # Ignore empty lines
    } else {
      return 0;			# Unrecognized line, return failure
    }
  }
  return 1;
}


# Mirc_Text_Format -- log format from saving a MIRC buffer
sub Mirc_Text_Format($$)
{
  my ($lines_ref, $records_ref) = @_;

  foreach (@$lines_ref) {
    if (/^\s*$/) {
      # Empty line, ignore
    } elsif (/^Start of \S+ buffer/) {
      # Skip this (should be first line)
    } elsif (/^End of \S+ buffer/) {
      # Skip this (should be last line)
    } elsif (/^\s*\*/) {
      # Skip /me lines
    } elsif (/^<([^ >]+)> (.*)$/) {
      push(@$records_ref, {type=>'i', id=>'', speaker=>$1, text=>$2});
    } elsif (/^( .*)$/ && @$records_ref) {	# Continuation line
      $$records_ref[@$records_ref-1]->{text} .= $1;
    } else {
      return 0;			# Unknown format
    }
  }
  return 1;
}


# Yahoo_IM_Format -- saved log from a Yahoo IM session
sub Yahoo_IM_Format($$)
{
  my ($lines_ref, $records_ref) = @_;

  foreach (@$lines_ref) {
    if (/^([^ :]+): (.*)$/) {
      push(@$records_ref, {type=>'i', id=>'', speaker=>$1, text=>$2});
    } elsif (/^\s*$/) {
      # Ignore empty lines
    } else {
      return 0;
    }
  }
  return 1;
}


# Bert_IRSSI_Format - Bert's IRSSI theme, based on elho, which should also work
sub Bert_IRSSI_Format($)
{
  my ($lines_ref, $records_ref) = @_;

  foreach (@$lines_ref) {
    next if /^---/;		# IRSSI comment about logging start/stop
    next if /^[][0-9:]+\s*[<>-]+ \| (\S+).*( has (?:joined|left).*)/;
    next if /^[][0-9:]+\s*«Quit» \| (\S+).* has signed off/;
    next if /^[][0-9:]+\s*«[^»]+» \|/; # IRSSI comment about users, topic, etc.
    next if /^[][0-9:]+\s*\* \|/;      # Skip a /me command
    next if /^\s*$/;		       # Skip empty line
    if (/^[][0-9:]+[\s@+%]*(\S+) \| (.*)/) {
      push(@$records_ref, {type=>'i', id=>'', speaker=>$1, text=>$2});
    } else {
      return 0;
    }
  }
  return 1;
}


# Plain_Text_Format -- a simple text format as a scribe might write in an editor
sub Plain_Text_Format($$)
{
  my ($lines_ref, $records_ref) = @_;

  # This format is meant for taking minutes without IRC. Example:
  #
  #     Topic: Closing issues
  #     Jim: I want to talk about issue 1.
  #     ... And 2, if possible.
  #     [General agreeement]
  #
  # Lines should not start with dates or times, or with bracketed
  # nicknames ("<...>"), as in typical IRC logs. E.g., the following
  # lines cause the parser to conclude that the input is *not*
  # Plain_Text_Format:
  #
  # *   09:34:14 <Sue> Topic: next meeting
  # *   2007-04-04 10:50 Jim: +1
  # *   <Aude> Not now.
  #
  foreach (@$lines_ref) {
    return 0 if /^[0-9:-]+[:-][0-9:-]/;		# Seems to start w/ a date/time
    return 0 if /^<[^ >]+> /;			# Seems to start with a <nick>
    if (/^(.+)$/) {				# Not empty
      push (@$records_ref, {type=>'i', id=>'', speaker=>'scribe', text=>$1});
    }
  }
  return 1;
}


# break_url -- apply -urlDisplay option to a URL
sub break_url($)
{
  my ($s) = @_;
  $s =~ s|/\b|/&zwnj;|g if $url_display eq 'break';
  $s =~ s|^(.{5}).*(.{6})$|$1…$2| if $url_display eq 'shorten';
  return $s;
}


# esc -- escape HTML delimiters (<>&"), optionally handle emphasis marks (_*/)
sub esc($;$$$)
{
  my ($s, $emphasis, $make_links, $break_urls) = @_;

  $s =~ s/&/&amp;/g;
  $s =~ s/</&lt;/g;
  $s =~ s/>/&gt;/g;
  $s =~ s/"/&quot;/g;

  if ($make_links) {		# Wrap Ralph-links and bare URLs in <a>
    $s =~ s/-&gt; *($urlpat) +(&quot;|'|)(.*?)\g2\s*$/<a href="$1">$3<\/a>/gi or
	$s =~ s/\b($urlpat)/"<a href=\"$1\">".break_url($1)."<\/a>"/gie;
  } elsif ($break_urls) {	# Shorten or break URLs
    $s =~ s/($urlpat)/break_url($1)/gie;
  }
  if ($emphasis) {
    $s =~ s{(^|\s)_([^\s_](?:[^_]*[^\s_])?)_(\s|$)}{$1<u>$2</u>$3}g;
    $s =~ s{(^|\s)/([^\s/](?:[^/]*[^\s/])?)/(\s|$)}{$1<em>$2</em>$3}g;
    $s =~ s{(^|\s)\*([^\s*](?:[^*]*[^\s*])?)\*(\s|$)}{$1<strong>$2</strong>$3}g;
  }
  return $s;
}


# is_cur_scribe -- true if $nick is in %$curscribes_ref
sub is_cur_scribe($$)
{
  my ($nick, $curscribes_ref) = @_;

  return $$curscribes_ref{lc($nick)} || $$curscribes_ref{'*'};
}
  

# Main body

$main::VERSION = '$Revision$'
  =~ s/\$Revision: //r
  =~ s/ \$//r;
my $versiondate = '$Date$'
  =~ s/\$Date: //r
  =~ s/ \$//r;

my @diagnostics;		# Collected warnings and other info
my %scribes;			# List of scribes
my %scribenicks;		# List of scribenicks (used if %scribes empty)
my @records;			# Array of parsed lines
my $date;			# Date of the meeting
my $actions = '';		# HTML-formatted list of links to actions
my $resolutions = '';		# HTML-formatted list of links to resolutions
my $issues = '';		# HTML-formatted list of links to issues
my $meeting = "(MEETING TITLE)"; # Name of the meeting (HTML-escaped)
my $prev_meeting = '';		# HTML-formatted link to previous meeting
my %present;			# List of participants
my %regrets;			# List of regrets
my $minutes_url;		# URL of the minutes according to RRSAgent
my $logging_url;		# URL of the log according to RRSAgent
my $id = 'x00';			# Generates unique IDs
my $topics = '';		# HTML-formatted table of contents
my $agenda = '';		# HTML-formatted link to an agenda
my $chair = '-';		# HTML-escaped name of meeting chair
my %lastspeaker;		# Current speaker (separate for each scribe)
my $speakerid = 's00';		# Generates unique ID for each speaker
my %speakers;			# Unique ID for each speaker
my $use_scribe = 0;		# 1 = interpret 'scribe:' as 'scribenick:'
my %namedanchors;		# Set of already used IDs for NamedAnchorsHere
my %curscribes;			# Indexes are the current scribenicks
my $agenda_icon = '<img alt="Agenda" title="Agenda" ' .
  'src="https://www.w3.org/StyleSheets/scribe2/chronometer.png">';
my $irclog_icon = '<img alt="IRC log" title="IRC log" ' .
  'src="https://www.w3.org/StyleSheets/scribe2/text-plain.png">';
my $previous_icon = '<img alt="Previous meeting" title="Previous meeting" ' .
  'src="https://www.w3.org/StyleSheets/scribe2/go-previous.png">';

my %options = ("team" => sub {$is_team = 1; $is_member = $is_fancy = 0},
	       "member" => sub {$is_member = 1; $is_team = $is_fancy = 0},
	       "fancy" => sub {$is_fancy = 1; $is_team = $is_member = 0},
	       "embedDiagnostics!" => \$embed_diagnostics,
	       "implicitContinuations!" => \$implicitcont,
	       "allowSpaceContinuation!" => \$spacecont,
	       "keepLines!" => \$keeplines,
	       "urlDisplay=s" => sub {
		 if ($_[1] =~ /^(?:break|shorten|full$)/i) {$url_display=$_[1]}
		 else {die "--urlDisplay must be break, shorten or full\n"}},
	       "final!" => \$final,
	       "draft!" => sub {$final = ! $_[1]},
	       "scribenick=s" => \$scribenick,
	       "dashTopics!" => \$dash_topics,
	       "useZakimTopics!" => \$use_zakim,
	       "scribeOnly!" => \$scribeonly,
	       "emphasis!", \$emphasis,
	       "oldStyle!" => \$old_style,
	       "logo:s" => \$logo,
	       "minutes=s" => \$minutes_url);
my @month = ('', 'January', 'February', 'March', 'April', 'May', 'June', 'July',
	     'August', 'September', 'October', 'November', 'December');

GetOptionsFromString($ENV{"SCRIBEOPTIONS"}, %options) if $ENV{"SCRIBEOPTIONS"};
GetOptions(%options) or pod2usage(2);

# Step 1: Read all lines into a temporary array and parse them into
# records, trying each parser in turn until one succeeds.
# Remove any CR, in case the file was saved under Windows.
#
do {
  my @input = map s/\r$//r, <>;
  do {@records = (); last if &$_(\@input, \@records);} foreach (@parsers);
  push(@diagnostics,'Input has an unknown format (or is empty).') if !@records;
};

# Step 2: Process s/old/new/ and i/where/what/ commands.
#
# First mark all s/// and i/// lines as 'c', so that they don't get
# changed by other s/// lines. Then loop over all lines again and
# apply the substitutions and insertions. Successful s/// and i///
# become of type 'o' (omit).
#
foreach (@records) {
  $_->{type} = 'c' if
      $_->{text} =~ /^ *(s|i)(\/|\|)(.*?)\2(.*?)(?:\2([gG])? *)?$/;
}

for (my $i = 0; $i < @records; $i++) {

  if ($records[$i]->{type} eq 'c' &&
      $records[$i]->{text} =~ /^ *(s|i)(\/|\|)(.*?)\2(.*?)(?:\2([gG])? *)?$/) {
    my ($cmd, $old, $new, $global) = ($1, $3, $4, $5);

    if ($cmd eq 'i') {				# i/where/what/
      my $j = $i - 1;
      $j-- until $j < 0 || ($records[$j]->{type} eq 'i' &&
			    $records[$j]->{text} =~ /\Q$old\E/);
      if ($j >= 0) {
	splice(@records, $j, 0,
	       {type=>'i',id=>'',speaker=>$records[$i]->{speaker},text=>$new});
	$i++;			# All records shifted by the splice
	$records[$i]->{type} = 'o';
	push(@diagnostics, 'Succeeded: ' . $records[$i]->{text});
      } else {
	push(@diagnostics, 'Failed: ' . $records[$i]->{text});
      }

    } elsif (! defined $global) {		# s/old/new/
      my $j = $i - 1;
      $j-- until $j < 0 || ($records[$j]->{type} eq 'i' &&
			    $records[$j]->{text} =~ s/\Q$old\E/$new/);

      push(@diagnostics,
	   ($j >= 0 ? 'Succeeded: ' : 'Failed: ') . $records[$i]->{text});
      $records[$i]->{type} = 'o' if $j >= 0; # Omit successful command

    } else {					# s/old/new/g or .../G
      my $n = 0;
      for (0 .. ($global eq 'g' ? $i-1 : @records-1)) {
	$records[$_]->{text} =~ s/\Q$old\E/$new/ and $n++ if
	    $records[$_]->{type} eq 'i';
      }
      push(@diagnostics,
	   ($n ? "Succeeded $n times: " : "Failed: ") . $records[$i]->{text});
      $records[$i]->{type} = 'o' if $n; # Omit successful command
    }
  }
}

# Step 3: Interpret each record, collect topics, actions, etc.
#
# First search for scribeOptions, as they may affect the whole log.
#
foreach my $p (@records) {
  if ($p->{text} =~ /^ *scribeoptions *: *(.*?) *$/i) {
    Getopt::Long::Configure("pass_through");
    my ($ret, $args) = GetOptionsFromString($1, %options);
    push(@diagnostics, 'Unknown option in scribeoptions: ' . join(' ', @$args))
	if scalar @$args;
    $p->{type} = 'o';			# Omit line from output
  }
}

# Now initialize $scribenick (if it wasn't given as a command line
# option), so it can be applied to the first lines. If no scribenick
# found, look for a scribe command instead. And if there is none, take
# as scribe the person who wrote the most lines.
#
my ($s, %count);
while (!defined $scribenick && (my ($i,$p) = each @records)) {
  $scribenick = $1 if $p->{text} =~ /^ *scribenick *: *(.*[^ ]) *$/i;
  $s = $1 if !defined $s && $p->{text}=~/^ *scribe *: *([^ ]+) *$/i;
  $count{lc $p->{speaker}}++
    if $p->{type} eq 'i' && $p->{speaker} ne 'RRSAgent';
}
$use_scribe = 1 if !defined $scribenick;
$scribenick = $s if !defined $scribenick;
if (!defined $scribenick) {
  $scribenick = (sort {$count{$b} <=> $count{$a}} sort keys %count)[0];
  # If still undef, it means there are no lines at all...
  $scribenick = '*' if !defined $scribenick;
  push(@diagnostics, "No scribenick or scribe found. Guessed: $scribenick");
}
%curscribes = map {$_ => 1} split(/ *, */, lc($scribenick));
$scribenicks{lc $_} = $_ foreach split(/ *, */, $scribenick);

# Interpret each line. %curscribes is the current set of scribes in lowercase.
# $lastspeaker is the current speaker, for use in continuation lines.
# $lastspeaker is set to foo whenever the scribe writes "foo: ...".
#
for (my $i = 0; $i < @records; $i++) {

  if ($records[$i]->{type} eq 'o') {
    # This record was already processed

  } elsif ($records[$i]->{text} =~ /^\s*$/) {
    $records[$i]->{type} = 'o';		# Omit empty line

  } elsif ($records[$i]->{text} =~ /^ *present *: *(.*?) *$/i) {
    %present = map { lc($_) => $_ } split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *present *\+:? *$/i) {
    $present{lc $records[$i]->{speaker}} = $records[$i]->{speaker};
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *present *\+:? *(.*?) *$/i) {
    $present{lc $_} = $_ foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *present *-:? *(.*?) *$/i) {
    delete $present{lc $_} foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *regrets *: *(.*?) *$/i) {
    %regrets = map { lc($_) => $_ } split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *regrets *\+:? *$/i) {
    $regrets{lc $records[$i]->{speaker}} = $records[$i]->{speaker};
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *regrets *\+:? *(.*?) *$/i) {
    $regrets{lc $_} = $_ foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *regrets *-:? *(.*?) *$/i) {
    delete $regrets{lc $_} foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *topic *: *(.*?) *$/i) {
    $records[$i]->{type} = 't';		# Mark as topic line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID
    $topics .= "<li><a href=\"#$id\">" . esc($1,$emphasis,0,1) . "</a></li>\n";

  } elsif ($dash_topics && $records[$i]->{text} =~ /^ *-+ *$/) {
    for (my $j = $i + 1; $j < @records; $j++) {
      if ($records[$j]->{speaker} eq $records[$i]->{speaker}) {
	$records[$i]->{type} = 't';
	$records[$i]->{text} = $records[$j]->{text} =~ s/^ *(.*?) *$/$1/r;
	$records[$i]->{id} = ++$id;	# Unique ID
	$topics .= "<li><a href=\"#$id\">".esc($1,$emphasis,0,1)."</a></li>\n";
	$records[$j]->{type} = 'o';
	last;
      }
    }

  } elsif ($records[$i]->{speaker} eq 'RRSAgent' &&
	   $records[$i]->{text} =~ / to generate ([^ #]+)/) {
    $minutes_url = $1;
    $records[$i]->{type} = 'o';		# Ignore this line

  } elsif ($records[$i]->{speaker} eq 'RRSAgent' &&
	   $records[$i]->{text}=~ /(?:[Ll]ogging to|recorded in|See) ([^ #]+)/){
    $logging_url = $1;
    $records[$i]->{type} = 'o';		# Ignore this line

  } elsif ($records[$i]->{text} =~ /^ *rrsagent,/i) {
    $records[$i]->{type} = 'o';		# Ignore this line

  } elsif ($records[$i]->{speaker} =~ /^RRSAgent$/) {
    # Ignore RRSAgent's list of actions, etc.
    $records[$i]->{type} = 'o';		# Ignore this line

  } elsif ($records[$i]->{text} =~ /^ *trackbot,/i) {
    $records[$i]->{type} = 'o';		# Ignore commands to trackbot

  } elsif ($records[$i]->{text} =~ /^ *action *: *(.*?) *$/i ||
	   $records[$i]->{text} =~ /^ *action +(\w+ *:.*?) *$/i ||
	   $records[$i]->{text} =~ /^ *action +([^ ]+ +to\b.*?) *$/i) {
    $records[$i]->{type} = 'a';		# Mark as action line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID
    $actions .= "<li><a href=\"#$id\">" . esc($1, $emphasis,0,1)."</a></li>\n";

  } elsif ($records[$i]->{text} =~ /^ *resol(?:ved|ution) *: *(.*?) *$/i) {
    $records[$i]->{type} = 'r';		# Mark as resolution line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID
    $resolutions .= "<li><a href=\"#$id\">".esc($1,$emphasis,0,1)."</a></li>\n";

  } elsif ($records[$i]->{text} =~ /^ *issue *: *(.*?) *$/i) {
    $records[$i]->{type} = 'u';		# Mark as issue line
    $records[$i]->{speaker} = 'Issue';
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID
    # It's a new issue. Add it to the list.
    $issues .= "<li><a href=\"#$id\">" . esc($1,$emphasis,0,1) . "</a></li>\n";

  } elsif ($records[$i]->{text} =~ /^ *(issue-\d+) *: *(.*?) *$/i) {
    $records[$i]->{type} = 'u';		# Mark as issue line
    $records[$i]->{speaker} = $1;
    $records[$i]->{text} = $2;
    $records[$i]->{id} = ++$id;		# Unique ID

  } elsif ($records[$i]->{text} =~ /^ *agenda *: *($urlpat) *$/i) {
    $agenda = '<a href="' . esc($1) . "\">$agenda_icon</a>\n";
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *agenda *: *(.*?) *$/i) {
    push(@diagnostics, "Found 'Agenda:' not followed by a URL: '$1'.");
    # $records[$i]->{type} = 'o';	# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *meeting *: *(.*?) *$/i) {
    $meeting = esc($1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *previous +meeting *: *($urlpat) *$/i){
    $prev_meeting = '<a href="' . esc($1) . "\">$previous_icon</a>\n";
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *previous +meeting *: *(.*?) *$/i) {
    push(@diagnostics,"Found 'Previous meeting:' not followed by a URL: '$1'.");
    # $records[$i]->{type} = 'o';	# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *chairs? *: *(.*?) *$/i) {
    $chair = esc($1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *date *: *(\d+ \w+ \d+)/i) {
    $date = $1;
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *scribe *: *(.*?) *$/i) {
    my $s = $1;
    $scribes{lc $s} = $s;		# Add to collected scribe list
    $records[$i]->{type} = 'o';		# Omit line from output
    %curscribes = map {$_ => 1} split(/ *, */, lc($s)) if $use_scribe;

  } elsif ($records[$i]->{text} =~ /^ *scribenick *: *(.*[^ ]) *$/i) {
    my $s = $1;
    %curscribes = map {$_ => 1} split(/ *, */, lc($s));
    $scribenicks{lc $_} = $_ foreach split(/ *, */, $s);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($use_zakim && $records[$i]->{speaker} eq 'Zakim' &&
	   $records[$i]->{text} =~ /^agendum \d+\. "(.*)" taken up/) {
    $records[$i]->{type} = 't';		# Mark as topic line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID
    $topics .= "<li><a href=\"#$id\">" . esc($1,$emphasis,0,1) . "</a></li>\n";

  } elsif ($use_zakim && $records[$i]->{speaker} eq 'Zakim' &&
	   $records[$i]->{text} =~ /the attendees (?:were|have been) (.*?),?$/){
    $present{lc $_} = $_ foreach split(/, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($use_zakim && $records[$i]->{speaker} eq 'Zakim' &&
	   $records[$i]->{text} =~ /^\.\.\. (.*?),?$/) {
    my $s = $1;				# See what this is a continuation of
    my $j = $i;
    $j-- while $j >= 0 && ($records[$j]->{text} =~ /^\.\.\. / ||
			   $records[$j]->{speaker} ne 'Zakim');
    if ($j >= 0 && $records[$j]->{text} =~ /the attendees (?:were|have been) /){
      $present{lc $_} = $_ foreach split(/, */, $s);
    } elsif ($j >= 0 && $records[$j]->{text} =~ /, you wanted /) {
      $records[$j]->{text} .= ' ' . $s;
    }
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($use_zakim && $records[$i]->{speaker} eq 'Zakim' &&
	   $records[$i]->{text} =~ /[^ ,]+, you wanted /) {
    # Leave Zakim's lines of the form: "Jim, you wanted to ..."

  } elsif ($use_zakim && $records[$i]->{speaker} eq 'Zakim') {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim

  } elsif ($use_zakim && $records[$i]->{text} =~ /^ *zakim,/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim

  } elsif ($use_zakim && $records[$i]->{text} =~ /^ *ack \w/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim

  } elsif ($use_zakim &&
	   $records[$i]->{text} =~ /^ *ag(g?)enda\s*\d*\s*[\+\-\=\?]/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim

  } elsif ($use_zakim &&
	   $records[$i]->{text} =~ /^ *(next|close)\s+ag(g?)end(a|(um))\s*\Z/i){
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim

  } elsif ($use_zakim &&
	   $records[$i]->{text} =~ /^ *open\s+ag(g?)end(a|(um))\s+\d+\Z/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim

  } elsif ($use_zakim &&
	   $records[$i]->{text} =~ /^ *take\s+up\s+ag(g?)end(a|(um))\s+\d+\Z/i){
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim

  } elsif ($use_zakim && $records[$i]->{text} =~ /^ *q(?:ueue)?\s*[-+=?]/i){
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim

  } elsif ($use_zakim && $records[$i]->{text} =~ /^ *[-+=?]\s*q(?:ueue)?\b/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim

  } elsif ($use_zakim && $records[$i]->{text} =~ /^ *clear\s+agenda\s*$/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim

  } elsif ($records[$i]->{text} =~ /^\s*namedanchorhere\s*:\s*(.*?)\s*$/i) {
    my $a = $1 =~ s/\s/_/gr;
    if ($a =~ /^$/) {
      push(@diagnostics, "Empty named anchor ignored.");
    } elsif ($a =~ /^x[0-9][0-9]+$/) {
      push(@diagnostics, "Named anchor \"$a\" ignored. (\"xNN\" is reserved.)");
    } elsif ($a =~ /^(?:(?:Action|Resolution)Summary|links|attendees|toc|meeting)$/) {
      push(@diagnostics, "Named anchor \"$a\" ignored. (The name is reserved.)");
    } elsif (exists $namedanchors{$a}) {
      push(@diagnostics, "Duplicate named anchor \"$a\" ignored.");
    } else {
      $records[$i]->{type} = 'n';
      $records[$i]->{id} = esc($a);
      $namedanchors{$a} = 1;
    }

  } elsif (is_cur_scribe($records[$i]->{speaker}, \%curscribes) &&
	   $records[$i]->{text} =~ /^\s*<$records[$i]->{speaker}>/i) {
    # Ralph's escape for a scribe's personal remarks: "<mynick> my opinion"
    $records[$i]->{text} =~ s/^.*?> ?//i;

  } elsif (is_cur_scribe($records[$i]->{speaker}, \%curscribes) &&
	   ($records[$i]->{text} =~ /^([^ <:]+) *: *(.*)$/ ||
	    (!$spacecont && $records[$i]->{text} =~ /^ *([^ <:]+) *: *(.*)$/))&&
	   $records[$i]->{text} !~ /^ *$urlpat/i) {	# ... and not a URL
    $records[$i]->{type} = 's';		# Mark as scribe line
    $lastspeaker{$records[$i]->{speaker}} = $1; # For any continuation lines
    $records[$i]->{speaker} = $1;
    $records[$i]->{text} = $2;
    $speakers{lc $1} = ++$speakerid if !exists $speakers{lc $1};

  } elsif (is_cur_scribe($records[$i]->{speaker}, \%curscribes) &&
	   defined $lastspeaker{$records[$i]->{speaker}} &&
	   (($implicitcont && $records[$i]->{text} =~ /^ *(.*?) *$/) ||
	    ($spacecont && $records[$i]->{text} =~ /^ +(.*?) *$/) ||
	    $records[$i]->{text} =~ /^ *(?:\.\.\.*|…) *(.*?) *$/)) {
    $records[$i]->{speaker} = $lastspeaker{$records[$i]->{speaker}};
    $records[$i]->{type} = 's';		# Mark as scribe line
    my $j = $i - 1; $j-- while $j > 0 && $records[$j]->{type} eq 'o';
    if ($j >= 0 && $records[$j]->{type} eq 's' &&
	$records[$j]->{speaker} eq $records[$i]->{speaker}) {
      # Concatenate previous and current line and remove previous line
      $records[$i]->{text} = $records[$j]->{text} . "\t" . $1;
      $records[$j]->{type} = 'o';	# Omit previous line from output
    } else {
      # Cannot concatenate with previous line, remove "..." instead.
      $records[$i]->{text} = $1;
    }

  } elsif (is_cur_scribe($records[$i]->{speaker}, \%curscribes) &&
	   $records[$i]->{type} eq 'c') {
    # It's a failed s/// command by the speaker.
    $records[$i]->{type} = 'd';		# Mark as descriptive text
    
  } elsif (is_cur_scribe($records[$i]->{speaker}, \%curscribes) &&
	   $records[$i]->{text} =~ /^ *-> *$urlpat/i) {
    # If the scribe used a Ralph-link (-> url ...), still allow continuations
    $records[$i]->{type} = 'd';		# Mark as descriptive text

  } elsif (is_cur_scribe($records[$i]->{speaker}, \%curscribes)) {
    $records[$i]->{type} = 'd';		# Mark as descriptive text
    $lastspeaker{$records[$i]->{speaker}} = undef; # No continuation expected
  }
}

# If date wasn't given, guess it from a URL, if any
if (!defined $date && defined $minutes_url &&
    $minutes_url =~ m|/(\d\d\d\d)/(\d\d)/(\d\d)-|) {
  $date = $3 . ' ' . $month[0+$2] . ' ' . $1;
} elsif (!defined $date && defined $logging_url &&
	 $logging_url =~ m|/(\d\d\d\d)/(\d\d)/(\d\d)-|) {
  $date = $3 . ' ' . $month[0+$2] . ' ' . $1;
} elsif (!defined $date) {
  $date = "";
  push(@diagnostics, "Found no dated URLs. You may need to use 'Date:'.");
}

# If there were no explicit "scribe:" commands, use the scribenicks instead.
%scribes = %scribenicks if !%scribes;

# If no present list was found, put a guess in the diagnostics.
if (!%present) {
  my %a;
  for (@records) {if ($_->{type} eq 's') {$a{lc $_->{speaker}} = $_->{speaker}}}
  push(@diagnostics, "Maybe present: " . join(", ", map($a{$_}, sort keys %a)));
}

# Step 4. Convert records to HTML and then fill a template.
#
# Each type of record is converted to a specific HTML fragment, with
# %1$s replaced by the speaker, %2$s by the ID and %3$s by the text.
#
# Also replace \t (i.e., placeholders for line breaks) as appropriate.
#
my %linepat = (
  a => "<p class=action id=%2\$s><strong>Action:</strong> %3\$s</p>\n",
  d => "<p class=summary>%3\$s</p>\n",
  i => $scribeonly ? '' : "<p class=irc><cite>&lt;%1\$s&gt;</cite> %3\$s</p>\n",
  c => "<p class=irc><cite>&lt;%1\$s&gt;</cite> %3\$s</p>\n",
  o => '',
  r => "<p class=resolution id=%2\$s><strong>Resolved:</strong> %3\$s</p>\n",
  s => "<p class=\"phone %4\$s\"><cite>%1\$s:</cite> %3\$s</p>\n",
  n => "<p class=anchor id=\"%2\$s\"><a href=\"#%2\$s\">⚓</a></p>\n",
  u => "<p class=issue id=%2\$s><strong>%1\$s:</strong> %3\$s</p>\n",
  t => "</section>\n\n<section>\n<h3 id=%2\$s>%3\$s</h3>\n");

my $minutes = '';
foreach my $p (@records) {
  # The last part generates nothing, but avoids warnings for unused args.
  my $line = sprintf $linepat{$p->{type}} . '%1$.0s%2$.0s%3$.0s%4$.0s',
    esc($p->{speaker}, 0), $p->{id}, esc($p->{text}, $emphasis, 1),
    $speakers{lc $p->{speaker}} // '';
  if ($keeplines) {$line =~ s/\t/<br>\n… /g;} else {$line =~ tr/\t/ /;}
  $minutes .= $line;
}

# Style sheets: 0 = default, 1 = alternate (= alternative).
#
my @stylesheets = $old_style & $is_team ?
  ([0, "Default", "https://www.w3.org/StyleSheets/base.css"],
   [0, "Default", "https://www.w3.org/StyleSheets/team.css"],
   [0, "Default", "https://www.w3.org/StyleSheets/team-minutes.css"],
   [0, "Default", "https://www.w3.org/2004/02/minutes-style.css"],
   [1, "New style", "https://www.w3.org/StyleSheets/scribe2/team.css"]) :
  $old_style && $is_member ?
  ([0, "Default", "https://www.w3.org/StyleSheets/base.css"],
   [0, "Default", "https://www.w3.org/StyleSheets/member.css"],
   [0, "Default", "https://www.w3.org/StyleSheets/member-minutes.css"],
   [0, "Default", "https://www.w3.org/2004/02/minutes-style.css"],
   [1, "New style", "https://www.w3.org/StyleSheets/scribe2/member.css"]) :
  $old_style ?
  ([0, "Default", "https://www.w3.org/StyleSheets/base.css"],
   [0, "Default", "https://www.w3.org/StyleSheets/public.css"],
   [0, "Default", "https://www.w3.org/2004/02/minutes-style.css"],
   [1, "New style", "https://www.w3.org/StyleSheets/scribe2/public.css"],
   [1, "Fancy", "https://www.w3.org/StyleSheets/scribe2/fancy.css"]) :
  $is_team ?
  ([0, "Default", "https://www.w3.org/StyleSheets/scribe2/team.css"],
   [1, "Old style", "https://www.w3.org/StyleSheets/base.css"],
   [1, "Old style", "https://www.w3.org/StyleSheets/team.css"],
   [1, "Old style", "https://www.w3.org/StyleSheets/team-minutes.css"],
   [1, "Old style", "https://www.w3.org/2004/02/minutes-style.css"]) :
  $is_member ?
  ([0, "Default", "https://www.w3.org/StyleSheets/scribe2/member.css"],
   [1, "Old style", "https://www.w3.org/StyleSheets/base.css"],
   [1, "Old style", "https://www.w3.org/StyleSheets/member.css"],
   [1, "Old style", "https://www.w3.org/StyleSheets/member-minutes.css"],
   [1, "Old style", "https://www.w3.org/2004/02/minutes-style.css"]) :
  !$is_fancy ?
  ([0, "Default", "https://www.w3.org/StyleSheets/scribe2/public.css"],
   [1, "Old style", "https://www.w3.org/StyleSheets/base.css"],
   [1, "Old style", "https://www.w3.org/StyleSheets/public.css"],
   [1, "Old style", "https://www.w3.org/2004/02/minutes-style.css"],
   [1, "Fancy", "https://www.w3.org/StyleSheets/scribe2/fancy.css"]) :
  ([0, "Fancy", "https://www.w3.org/StyleSheets/scribe2/fancy.css"],
   [1, "New style", "https://www.w3.org/StyleSheets/scribe2/public.css"],
   [1, "Old style", "https://www.w3.org/StyleSheets/base.css"],
   [1, "Old style", "https://www.w3.org/StyleSheets/public.css"],
   [1, "Old style", "https://www.w3.org/2004/02/minutes-style.css"]);

# Format some of the variables used in the template below
#
my $style = join("\n",
  map {"<link rel=\"" . ($_->[0] ? "alternate " : "") . "stylesheet\" " .
    "type=\"text/css\" title=\"$_->[1]\" href=\"$_->[2]\">"} @stylesheets);

$logo = "<p>$logo</p>\n\n" if defined $logo && $logo ne '';
$logo = '' if !defined $logo && $is_fancy;
$logo = '<p><a href="https://www.w3.org/"><img src="https://www.w3.org/Icons/w' .
  "3c_home\" alt=W3C border=0 height=48 width=72></a></p>\n\n" if !defined $logo;
my $draft = $final ? "" : "&ndash; DRAFT &ndash;<br>\n";
my $log = defined $logging_url?"<a href=\"$logging_url\">$irclog_icon</a>\n":"";
my $present = esc(join(", ", map($present{$_}, sort keys %present)));
my $regrets = esc(join(", ", map($regrets{$_}, sort keys %regrets)));
my $scribes = esc(join(", ", map($scribes{$_}, sort keys %scribes)));
my $diagnostics = !$embed_diagnostics || !@diagnostics ? "" :
  "<div class=diagnostics>\n<h2>Diagnostics<\/h2>\n" .
  join("", map {"<p class=warning>" . esc($_) . "</p>\n"} @diagnostics) .
  "</div>\n";

my $actiontoc = !$actions ? '' :
    "<li><a href=\"#ActionSummary\">Summary of Action Items</a></li>\n";
$actions = "\n<div id=ActionSummary>\n<h2>Summary of Action Items</h2>
<ol>\n$actions</ol>\n</div>\n" if $actions;

my $resolutiontoc = !$resolutions ? '' :
    "<li><a href=\"#ResolutionSummary\">Summary of Resolutions</a></li>\n";
$resolutions = "\n<div id=ResolutionSummary>\n<h2>Summary of Resolutions</h2>
<ol>\n$resolutions</ol>\n</div>\n" if $resolutions;

my $issuetoc = !$issues ? '' :
    "<li><a href=\"#IssueSummary\">Summary of Issues</a></li>\n";
$issues = "\n<div id=IssueSummary>\n<h2>Summary of Issues</h2>
<ol>\n$issues</ol>\n</div>\n" if $issues;

# And output the formatted HTML.
#
print "<!DOCTYPE html>
<html lang=\"en\">
<head>
<meta charset=utf-8>
<title>$meeting &ndash; $date</title>
$style
</head>

<body>
<header>
$logo<h1>$draft$meeting</h1>
<h2>$date</h2>

<div id=links>
$prev_meeting$agenda$log</div>
</header>

<nav>
<div id=attendees>
<h2>Attendees</h2>
<dl class=intro>
<dt>Present</dt><dd>$present</dd>
<dt>Regrets</dt><dd>$regrets</dd>
<dt>Chair</dt><dd>$chair</dd>
<dt>Scribe</dt><dd>$scribes</dd>
</dl>
</div>

<div id=toc>
<h2>Contents</h2>
<ul>
<li><a href=\"#meeting\">Meeting Minutes</a>
<ol>
$topics</ol>
</li>
$actiontoc$resolutiontoc$issuetoc</ul>
</div>
</nav>

<div id=meeting class=meeting>
<h2>Meeting Minutes</h2>
<section>$minutes</section>
</div>
$actions$resolutions$issues

<address>Minutes formatted by Bert Bos's <a
href=\"https://dev.w3.org/2002/scribe2/scribedoc.html\"
>scribe.perl</a> version $main::VERSION ($versiondate), a reimplementation
of David Booth's <a
href=\"https://dev.w3.org/2002/scribe/scribedoc.htm\"
>scribe.perl</a>. See <a
href=\"https://dev.w3.org/cvsweb/2002/scribe2/\">CVS log.</a></address>

$diagnostics</body>
</html>
";

print STDERR map("* $_\n", @diagnostics) if !$embed_diagnostics;

__END__

=head1 NAME

scribe.perl - Turn an IRC log of a meeting into minutes in HTML

=head1 SYNOPSIS

scribe.perl [options] [file ...]

  Options:
  --help		Brief help message
  --team		Use team style
  --member		Use member style
  --fancy		Use fancy style
  --embedDiagnostics	Put diagnostics in the minutes instead of on stderr
  --implicitContinuations	Continuation lines do not need `...'
  --allowSpaceContinuation	Allow initial space as well as `...'
  --keepLines		Do not rewrap lines (default)
  --urlDisplay=break	Allow URLs to break at slashes (default)
  --urlDisplay=shorten	Shorten URLs by omitting the middle part
  --urlDisplay=full	Do not shorten or break URLs
  --final		Omit the word `DRAFT' from the minutes
  --draft		Include the word `DRAFT' in the minutes (default)
  --scribenick		Initial list of scribe nicks, comma-separated
  --dashTopics		Allow a line of dashes to start a new topic
  --useZakimTopics	Parse Zakim's lines for agenda topics (default)
  --scribeOnly		Omit all text that is not written by a scribe
  --emphasis		Allow inline styles: _underline_ /italics/ *bold*
  --oldStyle		Use the style of scribe.perl version 1
  --minutes=I<URL>	Used to guess a date if the URL contains YYYY/MM/DD
  --logo=I<markup>	Replace the W3C link and logo with this HTML markup

You can use single dash (-) or double (--). Options are
case-insensitive and can be abbreviated. Some options can be negated
with `no' (e.g., --nokeeplines). For the full manual see
L<https://dev.w3.org/2002/scribe2/scribedoc.html>
