#!/usr/bin/perl
#
# Converts an IRC log to formatted minutes in HTML.
#
# See scribe2doc.html for the manual.
#
# This is a rewrite of David Booth's scribe.perl
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
# 3) Each line is interpreted, looking for topics, present & regrets,
# actions, resolutions, scribes, statements or summaries minuted by
# the scribes, and remarks by other people on IRC. Each record is
# modifed and classified accordingly.
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
# If type is 'o' (omit), the record is to be ignored.

use strict;
use warnings;
use Getopt::Long qw(GetOptionsFromString);
use 5.012;			# We use "each @ARRAY"
use locale;			# Sort using current locale

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


# esc -- escape HTML delimiters (<>&"),  optionally handle emphasis marks (_*/)
sub esc($$)
{
  my ($s, $emphasis) = @_;

  $s =~ s/&/&amp;/g;
  $s =~ s/</&lt;/g;
  $s =~ s/>/&gt;/g;
  $s =~ s/"/&quot;/g;
  if ($emphasis) {
    $s =~ s{(^|\s)_([^\s_](?:[^_]*[^\s_])?)_(\s|$)}{$1<u>$2</u>$3}g;
    $s =~ s{(^|\s)/([^\s/](?:[^/]*[^\s/])?)/(\s|$)}{$1<em>$2</em>$3}g;
    $s =~ s{(^|\s)\*([^\s*](?:[^*]*[^\s*])?)\*(\s|$)}{$1<strong>$2</strong>$3}g;
  }
  return $s;
}


# Main body

my $version = '$Revision$'
  =~ s/\$Revision: //r
  =~ s/ \$//r;
my $versiondate = '$Date$'
  =~ s/\$Date: //r
  =~ s/ \$//r;

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
# TODO: option --inputFormat

my @diagnostics;		# Collected warnings and other info
my %scribes;			# List of scribes
my %scribenicks;		# List of scribenicks (used if %scribes empty)
my @records;			# Array of parsed lines
my $date;			# Date of the meeting
my $actions = '';		# HTML-formatted list of actions
my $resolutions = '';		# HTML-formatted list of links to resolutions
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
my $speaker;			# Current speaker
my $speakerid = 's00';		# Generates unique ID for each speaker
my %speakers;			# Unique ID for each speaker
my $use_scribe = 0;		# 1 = interpret 'scribe:' as 'scribenick:'

my $urlpat = '(?:[a-z]+://|mailto:[^ <@]+\@|geo:[0-9.]|urn:[a-z0-9-]+:)[^ <]+';
my %options = ("team" => \$is_team,
	       "member" => \$is_member,
	       "fancy" => \$is_fancy,
	       "embedDiagnostics!" => \$embed_diagnostics,
	       "implicitContinuations!" => \$implicitcont,
	       "allowSpaceContinuation!" => \$spacecont,
	       "keepLines!" => \$keeplines,
	       "final!" => \$final,
	       "scribenick=s" => \$scribenick,
	       "dashTopics!" => \$dash_topics,
	       "useZakimTopics!" => \$use_zakim,
	       "scribeOnly!" => \$scribeonly,
	       "emphasis!", \$emphasis,
	       "oldStyle!" => \$old_style,
	       "minutes=s" => \$minutes_url);
my @month = ('', 'January', 'February', 'March', 'April', 'May', 'June', 'July',
	     'August', 'September', 'October', 'November', 'December');

if ($ENV{"SCRIBEOPTIONS"}) {
  my ($ret, $args) = GetOptionsFromString($ENV{"SCRIBEOPTIONS"}, %options);
  push(@diagnostics, 'Unknown options in environment variable SCRIBEOPTIONS: ' .
       join(' ', @$args)) if !$ret;
}
GetOptions(%options);

# Step 1: Read all lines into a temporary array and parse them into
# records, trying each parser in turn until one succeeds.
#
do {
  my @input = <>;
  do {@records = (); last if &$_(\@input, \@records);} foreach (@parsers);
  push(@diagnostics,'Input has an unknown format (or is empty).') if !@records;
};

# Step 2: Process s/old/new/ and i/where/what/ commands.
#
for (my $i = 0; $i < @records; $i++) {

  if ($records[$i]->{text} =~ /^ *(s|i)(\/|\|)(.*?)\2(.*?)(?:\2([gG])? *)?$/) {
    my ($cmd, $old, $new, $global) = ($1, $3, $4, $5);

    if ($cmd eq 'i') {				# i/where/what/
      my $j = $i - 1;
      $j-- until $j < 0 || $records[$j]->{text} =~ /\Q$old\E/;
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
      $j-- until $j < 0 || $records[$j]->{text} =~ s/\Q$old\E/$new/;
      if ($j >= 0) {
	push(@diagnostics, 'Succeeded: ' . $records[$i]->{text});
	$records[$i]->{type} = 'o';
      } else {
	push(@diagnostics, 'Failed: ' . $records[$i]->{text});
      }

    } else {					# s/old/new/g or .../G
      my $n = 0;
      $records[$_]->{text} =~ s/\Q$old\E/$new/ and $n++ for 0..$i-1;
      if ($global eq 'G') {
	$records[$_]->{text} =~ s/\Q$old\E/$new/ and $n++ for $i+1..@records-1;
      }
      push(@diagnostics,
	   ($n ? "Succeeded $n times: " : "Failed: ") . $records[$i]->{text});
      $records[$i]->{type} = 'o';
    }
  }
}

# Step 3: Interpret each record, collect topics, actions, etc.
#
# First search for scribeOptions, as they may affect the whole log.
#
foreach my $p (@records) {
  if ($p->{text} =~ /^ *scribeoptions *: *(.*?) *$/i) {
    my ($ret, $args) = GetOptionsFromString($1, %options);
    push(@diagnostics, 'Unknown options: ' . join(' ', @$args)) if !$ret;
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
  $scribenick = $1 if $p->{text} =~ /^ *scribenick *: *([^ ]+) *$/i;
  $s = $1 if !defined $s && $p->{text}=~/^ *scribe *: *([^ ]+) *$/i;
  $count{lc $p->{speaker}}++ if $p->{type} eq 'i';
}
$use_scribe = 1 if !defined $scribenick;
$scribenick = $s if !defined $scribenick;
if (!defined $scribenick) {
  $scribenick = (sort {$count{$b} <=> $count{$a}} sort keys %count)[0];
  # If still undef, it means there are no lines at all...
  push(@diagnostics, "No scribenick or scribe found. Guessed: $scribenick");
}
$scribenicks{lc $scribenick} = esc($scribenick, 0) if defined $scribenick;
$scribenick = lc($scribenick // '');

# Interpret each line. $scribenick is the current scribe in lowercase.
# $speaker is the current speaker, for use in continuation lines.
# $speaker is set to foo whenever the scribe writes "foo: ..." and set
# to undef when the scribe writes something that is not a continuation
# line.
#
for (my $i = 0; $i < @records; $i++) {

  if ($records[$i]->{type} eq 'o') {
    # This record was already processed

  } elsif ($records[$i]->{text} =~ /^ *present *: *(.*?) *$/i) {
    %present = map { lc($_) => $_ } split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *present *\+:? *$/i) {
    $present{lc $records[$i]->{speaker}} = $records[$i]->{speaker};
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *present *\+:? *(.*?) *$/i) {
    $present{lc $_} = $_ foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *present *-:? *(.*?) *$/i) {
    delete $present{lc $_} foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *regrets *: *(.*?) *$/i) {
    %regrets = map { lc($_) => $_ } split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *regrets *\+:? *$/i) {
    $regrets{lc $records[$i]->{speaker}} = $records[$i]->{speaker};
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *regrets *\+:? *(.*?) *$/i) {
    $regrets{lc $_} = $_ foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *regrets *-:? *(.*?) *$/i) {
    delete $regrets{lc $_} foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *topic *: *(.*?) *$/i) {
    $records[$i]->{type} = 't';		# Mark as topic line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID
    $topics .= "<li><a href=\"#$id\">" . esc($1, $emphasis) . "</a></li>\n";
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($dash_topics && $records[$i]->{text} =~ /^ *-- *$/) {
    for (my $j = $i + 1; $j < @records; $j++) {
      if ($records[$j]->{speaker} eq $records[$i]->{speaker}) {
	$records[$i]->{type} = 't';
	$records[$i]->{text} = $records[$j]->{text} =~ s/^ *(.*?) *$/$1/r;
	$records[$i]->{id} = ++$id;	# Unique ID
	$topics .= "<li><a href=\"#$id\">" . esc($1,$emphasis) . "</a></li>\n";
	$records[$j]->{type} = 'o';
	last;
      }
    }
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{speaker} eq 'RRSAgent' &&
	   $records[$i]->{text} =~ / to generate ([^ #]+)/) {
    $minutes_url = $1;
    $records[$i]->{type} = 'o';		# Ignore this line

  } elsif ($records[$i]->{speaker} eq 'RRSAgent' &&
	   $records[$i]->{text} =~ /(?:logging to|recorded in|See) ([^ #]+)/) {
    $logging_url = $1;
    $records[$i]->{type} = 'o';		# Ignore this line

  } elsif ($records[$i]->{text} =~ /^ *rrsagent,/i) {
    $records[$i]->{type} = 'o';		# Ignore this line
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{speaker} eq 'RRSAgent') {
    # Ignore RRSAgent's list of actions, etc.
    $records[$i]->{type} = 'o';		# Ignore this line

  } elsif ($records[$i]->{text} =~ /^ *trackbot,/i) {
    $records[$i]->{type} = 'o';		# Ignore commands to trackbot
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *action *: *(.*?) *$/i ||
	   $records[$i]->{text} =~ /^ *action +(\w+ *:.*?) *$/i ||
	   $records[$i]->{text} =~ /^ *action +([^ ]+ +to\b.*?) *$/i) {
    $records[$i]->{type} = 'a';		# Mark as action line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID
    $actions .= "<li><a href=\"#$id\">" . esc($1, $emphasis) . "</a></li>\n";
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *resol(?:ved|ution) *: *(.*?) *$/i) {
    $records[$i]->{type} = 'r';		# Mark as resolution line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID
    $resolutions .= "<li><a href=\"#$id\">".esc($1, $emphasis)."</a></li>\n";
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *agenda *: *($urlpat) *$/i) {
    $agenda = '<a href="' . esc($1, 0) . "\">Agenda</a>\n";
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *agenda *: *(.*?) *$/i) {
    push(@diagnostics, "Found 'Agenda:' not followed by a URL: '$1'.");
    # $records[$i]->{type} = 'o';	# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *meeting *: *(.*?) *$/i) {
    $meeting = esc($1, 0);
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *previous +meeting *: *($urlpat) *$/i){
    $prev_meeting = '<a href="' . esc($1, 0) . "\">Previous</a>\n";
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *previous +meeting *: *(.*?) *$/i) {
    push(@diagnostics,"Found 'Previous meeting:' not followed by a URL: '$1'.");
    # $records[$i]->{type} = 'o';	# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *chair *: *(.*?) *$/i) {
    $chair = esc($1, 0);
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *date *: *(\d+ \w+ \d+)/i) {
    # TODO: warn about unrecognized or impossible dates
    $date = $1;
    $records[$i]->{type} = 'o';		# Omit line from output
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *scribe *: *(.*?) *$/i) {
    $scribes{lc $1} = $1;		# Add to collected scribe list
    $records[$i]->{type} = 'o';		# Omit line from output
    $scribenick = lc $1 if $use_scribe;
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($records[$i]->{text} =~ /^ *scribenick *: *([^ ]+) *$/i) {
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;
    $scribenick = lc $1;
    $scribenicks{lc $1} = esc($1, 0);	# Add to collected scribenicks list
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($use_zakim && $records[$i]->{speaker} eq 'Zakim' &&
	   $records[$i]->{text} =~ /^agendum \d+\. "(.*)" taken up/) {
    $records[$i]->{type} = 't';		# Mark as topic line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID
    $topics .= "<li><a href=\"#$id\">" . esc($1, $emphasis) . "</a></li>\n";

  } elsif ($use_zakim && $records[$i]->{speaker} eq 'Zakim' &&
	   $records[$i]->{text} =~ /[^ ,]+, you wanted /) {
    # Leave Zakim's lines of the form: "Jim, you wanted to ..."

  } elsif ($use_zakim && $records[$i]->{speaker} eq 'Zakim') {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim

  } elsif ($use_zakim && $records[$i]->{text} =~ /^ *zakim,/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($use_zakim && $records[$i]->{text} =~ /^ *ack \w/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($use_zakim &&
	   $records[$i]->{text} =~ /^ *ag(g?)enda\s*\d*\s*[\+\-\=\?]/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($use_zakim &&
	   $records[$i]->{text} =~ /^ *(next|close)\s+ag(g?)end(a|(um))\s*\Z/i){
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($use_zakim &&
	   $records[$i]->{text} =~ /^ *open\s+ag(g?)end(a|(um))\s+\d+\Z/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($use_zakim &&
	   $records[$i]->{text} =~ /^ *take\s+up\s+ag(g?)end(a|(um))\s+\d+\Z/i){
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($use_zakim && $records[$i]->{text} =~ /^ *q\s*[\+\-\=\?]/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($use_zakim && $records[$i]->{text} =~ /^ *queue\s*[\+\-\=\?]/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif ($use_zakim && $records[$i]->{text} =~ /^ *clear\s+agenda\s*$/i) {
    $records[$i]->{type} = 'o';		# Ignore most conversations with Zakim
    $speaker = undef if lc($records[$i]->{speaker}) eq $scribenick;

  } elsif (lc($records[$i]->{speaker}) eq $scribenick &&
	   ($records[$i]->{text} =~ /^([^ <:]+) *: *(.*)$/ ||
	    (!$spacecont && $records[$i]->{text} =~ /^ *([^ <:]+) *: *(.*)$/))&&
	   $records[$i]->{text} !~ /^ *$urlpat/i) {	# ... and not a URL
    $records[$i]->{type} = 's';		# Mark as scribe line
    $records[$i]->{speaker} = $1;
    $records[$i]->{text} = $2;
    $speakers{lc $1} = ++$speakerid if !defined $speakers{lc $1};
    $speaker = $1;			# Remember for use in continuation lines

  } elsif (lc($records[$i]->{speaker}) eq $scribenick && defined $speaker &&
	   ($implicitcont || $records[$i]->{text} =~ /^ *(?:\.\.\.*|…) *(.*)$/
	    || ($spacecont && $records[$i]->{text} =~ /^ +(.*)$/))) {
    $records[$i]->{speaker} = $speaker; # Same speaker as previously
    $records[$i]->{type} = 's';		# Mark as scribe line
    my $j = $i - 1; $j-- while $j > 0 && $records[$j]->{type} eq 'o';
    if ($j >= 0 && $records[$j]->{type} eq 's') {
      # Concatenate previous and current line and remove previous line
      $records[$i]->{text} = $records[$j]->{text} . "\t" . $1;
      $records[$j]->{type} = 'o';	# Omit previous line from output
    } else {
      # Cannot concatenate with previous line, remove "..." instead.
      $records[$i]->{text} =~ s/^ *(?:\.\.\.*|…)? *//;
    }

  } elsif (lc($records[$i]->{speaker}) eq $scribenick) {
    $records[$i]->{type} = 'd';		# Mark as descriptive text
    $speaker = undef;			# No continuation line expected
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
  my %speakers;
  foreach (@records) {if ($_->{type} eq 's') {$speakers{$_->{speaker}} = 1;}}
  push(@diagnostics, "Maybe present: " . join(", ", sort keys %speakers));
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
  o => '',
  r => "<p class=resolution id=%2\$s><strong>Resolved:</strong> %3\$s</p>\n",
  s => "<p class=\"phone %4\$s\"><cite>%1\$s:</cite> %3\$s</p>\n",
  t => "</section>\n<section>\n<h3 id=%2\$s>%3\$s</h3>\n");

my $minutes = '';
foreach my $p (@records) {
  # The last part generates nothing, but avoids warnings for unused args.
  my $line = sprintf $linepat{$p->{type}} . '%1$.0s%2$.0s%3$.0s%4$.0s',
    esc($p->{speaker}, 0), $p->{id}, esc($p->{text}, $emphasis),
    $speakers{lc $p->{speaker}} // '';
  if ($keeplines) {$line =~ s/\t/<br>\n… /g;} else {$line =~ s/\t/ /g;}

  # Link Ralph-links and bare URLs
  $line =~ s/-&gt; *($urlpat) +([^<]+)/<a href="$1">$2<\/a>/gi or
    $line =~ s/-&gt; *($urlpat) +"([^"<]*)/<a href="$1">$2<\/a>/gi or
    $line =~ s/-&gt; *($urlpat) +'([^'<]*)/<a href="$1">$2<\/a>/gi or
    $line =~ s/\b($urlpat)/<a href="$1">$1<\/a>/gi;

  $minutes .= $line;
}

my @stylesheets = $old_style & $is_team ?
  ("https://www.w3.org/StyleSheets/base.css",
   "https://www.w3.org/StyleSheets/team.css",
   "https://www.w3.org/StyleSheets/team-minutes.css",
   "https://www.w3.org/2004/02/minutes-style.css") :
  $old_style && $is_member ?
  ("https://www.w3.org/StyleSheets/base.css",
   "https://www.w3.org/StyleSheets/member.css",
   "https://www.w3.org/StyleSheets/member-minutes.css",
   "https://www.w3.org/2004/02/minutes-style.css") :
  $old_style ?
  ("https://www.w3.org/StyleSheets/base.css",
   "https://www.w3.org/StyleSheets/public.css",
   "https://www.w3.org/2004/02/minutes-style.css") :
  $is_team ? ("https://www.w3.org/StyleSheets/scribe2/team.css") :
  $is_member ? ("https://www.w3.org/StyleSheets/scribe2/member.css") :
  !$is_fancy ? ("https://www.w3.org/StyleSheets/scribe2/public.css") :
  ("https://www.w3.org/StyleSheets/scribe2/fancy.css");

# Format some of the variables used in the template below
#
my $style = join("\n",
  map {"<link rel=stylesheet type=\"text/css\" href=\"$_\">"} @stylesheets);
my $logo = !$is_fancy ?
  '<a href="https://www.w3.org/"><img src="https://www.w3.org/Icons/w3c_home" ' .
  'alt=W3C border=0 height=48 width=72></a>' : '';
my $draft = $final ? "" : "&ndash; DRAFT &ndash;<br>\n";
my $log = defined $logging_url ? "<a href=\"$logging_url\">IRC log</a>\n" : "";
my $present = esc(join(", ", sort values %present), 0);
my $regrets = esc(join(", ", sort values %regrets), 0);
my $scribes = esc(join(", ", values %scribes), 0);
my $diagnostics = !$embed_diagnostics ? "" :
  "<h2>Diagnostics<\/h2>\n" .
  join("", map {"<p class=warning>" . esc($_, 0) . "</p>\n"} @diagnostics);

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
<p>$logo</p>

<h1>$draft$meeting</h1>
<h2>$date</h2>

<div id=links>
$agenda$log$prev_meeting</div>
</header>

<nav>
<div id=attendees>
<h2>Attendees</a></h2>
<dl class=intro>
<dt>Present</dt><dd>$present</dd>
<dt>Regrets</dt><dd>$regrets</dd>
<dt>Chair</dt><dd>$chair </dd>
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
<li><a href=\"#ActionSummary\">Summary of Action Items</a></li>
<li><a href=\"#ResolutionSummary\">Summary of Resolutions</a></li>
</ul>
</div>
</nav>

<div id=meeting class=meeting>
<h2>Meeting Minutes</h2>
<section>$minutes</section>
</div>

<div id=ActionSummary>
<h2>Summary of Action Items</a></h2>
<ol>
$actions</ol>
</div>

<div id=ResolutionSummary>
<h2>Summary of Resolutions</a></h2>
<ol>
$resolutions</ol>
</div>

<address>Minutes formatted by Bert Bos's <a
href=\"https://dev.w3.org/2002/scribe2/scribedoc.html\"
>scribe.perl</a> version $version ($versiondate), a reimplementation
of David Booth's <a
href=\"https://dev.w3.org/2002/scribe/scribedoc.htm\"
>scribe.perl</a>. See <a
href=\"https://dev.w3.org/cvsweb/2002/scribe2/\">CVS log.</a></address>

<div class=diagnostics>
$diagnostics</div>
</body>
</html>
";

print STDERR map("* $_\n", @diagnostics) if !$embed_diagnostics;
