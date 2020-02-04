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
# TODO: Make "next meeting" accept a date ("7 Aug") or a period ("in 2
# weeks") and infer a URL?
#
# TODO: If trackbot assigns a number ("ISSUE-3") to an issue, use that
# number instead of the generic "Issue". Also use it in the
# #IssueSummary.
#
# TODO: An option to omit the special handling of W3C's bots
# (currently zakim, rrsagent and trackbot).
#
# TODO: Make commands such as scribeoptions:-implicit and
# scribeoptions:-allowspace apply only until they are overridden by
# another?
#
# TODO: A way to allow a scribe to write "A: 12 votes", where "A" is
# *not" interpreted as a speaker. Maybe: "A\:", ":A:", "A::"?
#
# TODO: RRSAgent has commands to edit or drop actions (because it
# doesn't understand s///). Should we support those?
#
# Copyright © 2017-2019 World Wide Web Consortium, (Massachusetts Institute
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


# Conversion proceeds in six steps:
#
# 1) Various parsers are tried to convert the lines of the input
# into an array of records (see below for the structure of the
# records).
#
# 2) Processing of "s/old/new/" and "i/where/what/" commands.
#
# 3) Scanning for embedded scribeOptions, as they may affect the parsing.
#
# 4) Finding the initial scribe, from a command line option or by
# scanning for the first scribe/scribenick command.
#
# 5) Each record is interpreted, looking for topics, present & regrets,
# actions, resolutions, scribes, statements or summaries minuted by
# the scribes, and remarks by other people on IRC. Each record is
# modified and classified accordingly.
#
# 6) The array of records is converted to an HTML fragment and that
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
# if type is 'u' (issue), <text> is an issue, <id> a unique ID.
# If type is 'c' (change), the record is a s/// or i/// not (yet) successful
# If type is 'o' (omit), the record is to be ignored.
# If type is 'n' (named anchor), the record is a target anchor.
# If type is 'b' ('bot), the record is info from trackbot.
# If type is 'B' ('bot), <text> is info from trackbot about an issue <id>.

use strict;
use warnings;
use Getopt::Long qw(GetOptionsFromString :config auto_version auto_help);
use Pod::Usage;
use v5.16;			# We use "each @ARRAY" (5.012) and fc (5.16)
use locale;			# Sort using current locale
use open ':utf8';		# Open all files assuming they are UTF-8
use utf8;			# This script contains characters in UTF-8


my $urlpat= '(?:[a-z]+://|mailto:[^\s<@]+\@|geo:[0-9.]|urn:[a-z0-9-]+:)[^\s<]+';
# $scribepat is something like "foo" or "foo = John Smith" or "foo/John Smith".
my $scribepat = '([^ ,/=]+) *(?:[=\/] *([^ ,](?:[^,]*[^ ,])?) *)?';
# A speaker name doesn't contain [ ":>] and doesn't start with "..".
my $speakerpat = '(?:[^. :">]|\.[^. :">])[^ :">]*';
# Some words are unlikely to be speaker names
my $specialpat = '(?:propos(?:ed|al)|issue-\d+|action-\d+)';

# Command line options:
my $styleset = 'public';	# Or 'team', 'member' or 'fancy'
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
my $stylesheet;			# URL of style sheet, undef = use defaults


# Each parser takes a reference to an array of text lines (without
# newlines) and a reference to an array of records. It returns 0
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
	       \&Yahoo_IM_Format, \&Bert_IRSSI_Format, \&Irssi_Format,
	       \&Plain_Text_Format);


# RRSAgent_text_format -- parse an IRC log as generated by RRSAgent
sub RRSAgent_text_format($$)
{
  my ($lines_ref, $records_ref) = @_;

  foreach (@$lines_ref) {
    if (/^(?:\d\d:\d\d:\d\d )?<([^ >]+)> \1 has (joined|left) /) {
      # Ignore lines like "<jfm> jfm has joined #foo"
    } elsif (/^(?:\d\d:\d\d:\d\d )?<([^ >]+)> \1 has changed the topic to: /) {
      # Ignore lines like "<jfm> jfm has changed the top to:..."
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


# Irssi_Format - logs from Coralie's Irssi
sub Irssi_Format($)
{
  my ($lines_ref, $records_ref) = @_;

  foreach (@$lines_ref) {
    next if /^---/;		 # IRSSI comment about logging start/stop
    next if /^[0-9:TZ-]+\s+-!-/; # Skip join/leave and other info
    next if /^[0-9:TZ-]+\s+\*/;	 # Skip a /me command
    next if /^\s*$/;		 # Skip empty line
    if (/^[0-9:TZ-]+\s+<([^>]+)> (.*)/) {
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


# fc_uniq -- return the list of case-insensitively distinct strings in a list
sub fc_uniq(@)
{
  my %seen;
  return grep {!$seen{fc $_}++} @_;
}


# break_url -- apply -urlDisplay option to a URL
sub break_url($)
{
  my ($s) = @_;

  # HTML delimiters are already escaped.
  if ($url_display eq 'break') {
    $s =~ s|/\b|/&zwnj;|g;
  } elsif ($url_display eq 'shorten') {
    $s =~ s/^((?:[^&]|&[^;]+;){5})(?:[^&]|&[^;]+;)*((?:[^&]|&[^;]+;){6})$/$1…$2/;
  }
  return $s;
}


# mklink -- return HTML for a URL with anchortext: link, image or just text
sub mklink($$$$)
{
  my ($link, $type, $url, $anchortext) = @_;
  # $link determines whether to make a link (>0) or just show the text (<0).
  # $type determines whether to make a text ("->") or an image ("-->").

  $url = esc($url);
  if ($link > 0) {
    my $s = '<a href="' . $url . '">';
    if ($type eq '-->') {
      $s .= '<img src="' . $url . '" alt="' . esc($anchortext) . '">';
    } elsif ($anchortext ne '') {
      $s .= esc($anchortext, $emphasis);
    } else {
      $s .= break_url($url); # Otherwise the URL itself is the anchor text
    }
    return "$s</a>";
  } else {
    return $anchortext ne '' ? esc($anchortext) : break_url($url);
  }
}


# esc -- escape HTML delimiters (<>&"), optionally handle emphasis & Ralph links
sub esc($;$$$);
sub esc($;$$$)
{
  my ($s, $emph, $link, $break_urls) = @_;
  my ($replacement, $pre, $url, $post, $pre1, $post1, $type, $anchor);

  if ($link) {
    # Wrap Ralph-links and bare URLs in <a>.
    # 1a) A double-quoted Ralph link: ... -> URL "ANCHOR" ...
    # 1b) A single-quoted Ralph link: ... -> URL 'ANCHOR' ...
    # 1a) An unquoted Ralph link: ... -> URL ANCHOR
    # 2) A Xueyuan link: ANCHOR -> URL
    # 3) An Ivan link: ... -> ANCHOR URL ...
    # 4a) A double-quoted inverted Xueyuan link: ... URL -> "ANCHOR" ...
    # 4b) A single-quoted inverted Xueyuan link: ... URL -> 'ANCHOR' ...
    # 4c) An unquoted inverted Xueyuan link: ... URL -> ANCHOR
    # 5) A bare URL: ... URL ...
    # With --> instead of ->, the link is embedded as an image (<img>).
    # If $link < 0, omit the <a> tag and just insert the text or image.

    # Loop until we found all URLs.
    $replacement = '';
    while (($pre, $url, $post) = $s =~ /^(.*?)($urlpat)(.*)$/) {
      # Look for "->" or "-->" before or after the URL.
      if (($type, $anchor) = $pre =~ /(--?>) *([^ ].*?) *$/) {	# Ivan link
    	$replacement .= esc($`, $emph) . mklink($link, $type, $url, $anchor);
    	$s = $post;
      } elsif (($pre1, $type) = $pre =~ /^(.*?)(--?>) *$/) {
	# Maybe Ralph or Xueyuan
    	if ($post =~ /^ *(\"|\')(.*?)\g1/) { # Quoted Ralph link
    	  $replacement .= esc($pre1, $emph) . mklink($link, $type, $url, $2);
    	  $s = $';
    	} elsif ($post =~ /^ *([^ ].*?) *$/) {	# Unquoted Ralph link
    	  $replacement .= esc($pre1, $emph) . mklink($link, $type, $url, $1);
    	  $s = '';
    	} elsif ($pre1 =~ /^ *([^ ].*?) *$/) {	# Xueyuan link
    	  $replacement .= mklink($link, $type, $url, $1);
    	  $s = $post;
    	} else {				# Missing anchor text
    	  $replacement .= esc($pre1, $emph) . mklink($link, $type, $url, '');
    	  $s = $post;
    	}
      } elsif (($type, $post1) = $post =~ /^ *(--?>)(.*)$/) {
	# Maybe inverted Xueyuan
	if ($post1 =~ /^ *(\"|\')(.*?)\g1/) { # Quoted inverted Xueyuan
	  $replacement .= esc($pre, $emph) . mklink($link, $type, $url, $2);
	  $s = $';
	} else {				# Unquoted inverted Xueyuan link
	  $post1 =~ /^ *(.*?) *$/;
	  $replacement .= esc($pre, $emph) . mklink($link, $type, $url, $1);
	  $s = '';
	}
      } else {					# Bare URL.
    	$replacement .= esc($pre, $emph) . mklink($link, '->', $url, '');
    	$s = $post;
      }
    }
    $s = $replacement . esc($s, $emph);
  } elsif ($break_urls) {	# Shorten or break URLs
    $s = esc($s, $emph);
    $s =~ s/($urlpat)/break_url($1)/gie;
  } else {
    $s =~ s/&/&amp;/g;
    $s =~ s/</&lt;/g;
    $s =~ s/>/&gt;/g;
    $s =~ s/"/&quot;/g;
    if ($emph) {
      $s =~ s{(^|\s)_([^\s_](?:[^_]*[^\s_])?)_(\s|$)}{$1<u>$2</u>$3}g;
      $s =~ s{(^|\s)/([^\s/](?:[^/]*[^\s/])?)/(\s|$)}{$1<em>$2</em>$3}g;
      $s =~ s{(^|\s)\*([^\s*](?:[^*]*[^\s*])?)\*(\s|$)}{$1<strong>$2</strong>$3}g;
      $s =~ s{(?:^|[^-])\K--&gt;}{⟶}g;	# "-->" not preceded by a "-"
      $s =~ s{(?:^|[^-])\K-&gt;}{→}g;	# "->" not preceded by a "-"
      $s =~ s{(?:^|[^=])\K==&gt;}{⟹}g; # "==>" not preceded by a "="
      $s =~ s{(?:^|[^=])\K=&gt;}{⇒}g;	# "=>" not preceded by a "="
      $s =~ s{&lt;--(?!-)}{⟵}g;		# "<--" not followed by a "-"
      $s =~ s{&lt;-(?!-)}{←}g;		# "<-" not followed by a "-"
      $s =~ s{&lt;==(?!=)}{⟸}g;	# "<==" not followed by a "="
      $s =~ s{&lt;=(?!=)}{⇐}g;		# "<=" not followed by a "="
      $s =~ s{:-\)}{☺}g;
      $s =~ s{;-\)}{😉}g;
      $s =~ s{:-\(}{☹}g;
      $s =~ s{:-/}{😕}g;
      $s =~ s{,-\)}{😜}g;
      $s =~ s{\\o/}{🙆}g;
      $s =~ s{/o\\}{🙎}g;
    }
  }
  return $s;
}


# is_cur_scribe -- true if $nick is in %$curscribes_ref
sub is_cur_scribe($$)
{
  my ($nick, $curscribes_ref) = @_;

  return $$curscribes_ref{fc($nick)} || $$curscribes_ref{'*'};
}


# Main body
my $revision = '$Revision: 107 $'
  =~ s/\$Revision: //r
  =~ s/ \$//r;
my $versiondate = '$Date: Tue Feb  4 12:47:25 2020 UTC $'
  =~ s/\$Date: //r
  =~ s/ \$//r;

my @diagnostics;		# Collected warnings and other info
my %scribes;			# List of scribes
my @records;			# Array of parsed lines
my $date;			# Date of the meeting
my $meeting = "(MEETING TITLE)"; # Name of the meeting (HTML-escaped)
my $prev_meeting = '';		# HTML-formatted link to previous meeting
my $next_meeting = '';		# HTML-formatted link to next meeting
my %present;			# List of participants
my %regrets;			# List of regrets
my $minutes_url;		# URL of the minutes according to RRSAgent
my $logging_url;		# URL of the log according to RRSAgent
my $id = 'x00';			# Generates unique IDs
my $agenda = '';		# HTML-formatted link to an agenda
my %chairs;			# List of meeting chairs
my %lastspeaker;		# Current speaker (separate for each scribe)
my $speakerid = 's00';		# Generates unique ID for each speaker
my %speakers;			# Unique ID for each speaker
my %namedanchors;		# Set of already used IDs for NamedAnchorsHere
my %curscribes;			# Indexes are the current scribenicks
my $agenda_icon = '<img alt="Agenda." title="Agenda" ' .
  'src="https://www.w3.org/StyleSheets/scribe2/chronometer.png">';
my $irclog_icon = '<img alt="IRC log." title="IRC log" ' .
  'src="https://www.w3.org/StyleSheets/scribe2/text-plain.png">';
my $previous_icon = '<img alt="Previous meeting." title="Previous meeting" ' .
  'src="https://www.w3.org/StyleSheets/scribe2/go-previous.png">';
my $next_icon = '<img alt="Next meeting." title="Next meeting" ' .
  'src="https://www.w3.org/StyleSheets/scribe2/go-next.png">';
my $w3clogo = '<a href="https://www.w3.org/"><img src="https://www.w3.org/' .
  'StyleSheets/TR/2016/logos/W3C" alt=W3C border=0 height=48 width=72></a>';

my %bots = (fc('RRSAgent') => 1, # Nicks that probably aren't scribe
	    fc('trackbot') => 1,
	    fc('agendabot') => 1,
	    fc('Zakim') => 1);

my %options = ("team" => sub {$styleset = 'team'},
	       "member" => sub {$styleset = 'member'},
	       "fancy" => sub {$styleset = 'fancy'},
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
	       "emphasis!" => \$emphasis,
	       "oldStyle!" => \$old_style,
	       "stylesheet:s" => \$stylesheet,
	       "logo:s" => \$logo,
	       "nologo" =>sub {$logo = ''},
	       "minutes=s" => \$minutes_url);
my @month = ('', 'January', 'February', 'March', 'April', 'May', 'June', 'July',
	     'August', 'September', 'October', 'November', 'December');

# The "use open" pragma takes care of setting a UTF8 layer on newly
# opened files from the command line, but STDIN is already open, so it
# needs a binmode() command.
binmode(STDIN, ':utf8');
binmode(STDOUT, ':utf8');
binmode(STDERR, ':utf8');

GetOptionsFromString($ENV{"SCRIBEOPTIONS"}, %options) if $ENV{"SCRIBEOPTIONS"};
GetOptions(%options) or pod2usage(2);

# Step 1: Read all lines into a temporary array and parse them into
# records, trying each parser in turn until one succeeds.
# Remove carriage returns and newlines from each line first.
#
do {
  my @input = map tr/\r\n//dr, <>;
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

# Step 3: Search for scribeOptions, as they may affect the whole log.
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

# Step 4: Find the initial scribe(s).
#
# The first scribe/scribenick command is also assumed to apply to the
# lines that come before it, so search for that first command (unless
# --scribenick was given on the command line). If no command is found,
# assume the person who typed most was the scribe. And if nobody typed
# anything, set the scribe to '*'.
#
my %count;
while (!defined $scribenick && (my ($i,$p) = each @records)) {
  if ($p->{text} =~ /^ *scribe(?:nick)? * \+:? *$/i) {
    $scribenick = $p->{speaker};
  } elsif ($p->{text} =~ /^ *scribe(?:nick)? *(?::|\+:?) *([^ ].*?) *$/i) {
    $scribenick = $1;
  } else {
    $count{$p->{speaker}}++ if $p->{type} eq 'i' && !$bots{fc($p->{speaker})};
  }
}
if (!defined $scribenick) {
  $scribenick = (sort {$count{$b} <=> $count{$a}} sort keys %count)[0];
  # If still undef, it means there are no lines at all...
  $scribenick = '*' if !defined $scribenick;
  push(@diagnostics, "No scribenick or scribe found. Guessed: $scribenick");
}
foreach (split(/ *, */, $scribenick)) {
  if (/^$scribepat$/ or /^(.+)$/) {
    $scribes{fc $1} = $2 // $1;
    $curscribes{fc $1} = 1;
  }
}

# Step 5: Interpret each record, collect topics, actions, etc.
#
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
    if ($records[$i]->{speaker} eq 'Zakim' && !$use_zakim) {} # Ignore Zakim?
    elsif ($1 eq '(no one)') {%present = ()}
    else {%present = map {fc($_) => $_} split(/ *, */, $1)}
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *present *\+:? *$/i) {
    $present{fc $records[$i]->{speaker}} = $records[$i]->{speaker};
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *present *\+:? *(.*?) *$/i) {
    $present{fc $_} = $_ foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *present *-:? *(.*?) *$/i) {
    delete $present{fc $_} foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *regrets? *: *(.*?) *$/i) {
    %regrets = map { fc($_) => $_ } split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *regrets? *\+:? *$/i) {
    $regrets{fc $records[$i]->{speaker}} = $records[$i]->{speaker};
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *regrets? *\+:? *(.*?) *$/i) {
    $regrets{fc $_} = $_ foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *regrets? *-:? *(.*?) *$/i) {
    delete $regrets{fc $_} foreach split(/ *, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *topic *: *(.*?) *$/i) {
    $records[$i]->{type} = 't';		# Mark as topic line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID

  } elsif ($dash_topics && $records[$i]->{text} =~ /^ *-+ *$/) {
    for (my $j = $i + 1; $j < @records; $j++) {
      if ($records[$j]->{speaker} eq $records[$i]->{speaker}) {
	$records[$i]->{type} = 't';
	$records[$i]->{text} = $records[$j]->{text} =~ s/^ *(.*?) *$/$1/r;
	$records[$i]->{id} = ++$id;	# Unique ID
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

  } elsif ($records[$i]->{speaker} eq 'RRSAgent') {
    # Ignore RRSAgent's list of actions, etc.
    $records[$i]->{type} = 'o';		# Ignore this line

  } elsif ($records[$i]->{text} =~ /^ *action *: *(.*?) *$/i ||
	   $records[$i]->{text} =~ /^ *action +(\pL\w* *:.*?) *$/i ||
	   $records[$i]->{text} =~ /^ *action +([^ ]+ +to\b.*?) *$/i) {
    $records[$i]->{type} = 'a';		# Mark as action line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID

  } elsif ($records[$i]->{text} =~ /^ *resol(?:ved|ution) *: *(.*?) *$/i) {
    $records[$i]->{type} = 'r';		# Mark as resolution line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID

  } elsif ($records[$i]->{text} =~ /^ *issue *: *(.*?) *$/i) {
    $records[$i]->{type} = 'u';		# Mark as issue line
    $records[$i]->{text} = $1;
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

  } elsif ($records[$i]->{text} =~ /^ *next +meeting *: *($urlpat) *$/i){
    $next_meeting = '<a href="' . esc($1) . "\">$next_icon</a>\n";
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *(previous|next) +meeting *: *(.*?) *$/i) {
    push(@diagnostics,"Found '$1 meeting:' not followed by a URL: '$2'.");
    # $records[$i]->{type} = 'o';	# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *chairs? *-:? *$/i) {
    delete $chairs{fc $records[$i]->{speaker}}; # Remove speaker from chairs
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *chairs? *-:? *(.*?) *$/i) {
    delete $chairs{fc $_} foreach (split(/ *, */, $1)); # Remove given chairs
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *chairs? *\+:? *$/i) {
    my $s = $records[$i]->{speaker};
    $chairs{fc $s} = $s;		# Add to collected chairs
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *chairs? *: *$/i) {
    push(@diagnostics, "Ignored empty command \"$records[$i]->{text}\"");

  } elsif ($records[$i]->{text} =~ /^ *chairs? *(:|\+:?) *(.*?) *$/i) {
    %chairs = () if $1 eq ':';		# Reset the list of chairs
    $chairs{fc $_} = $_ foreach (split(/ *, */, $2)); # Add all to chairs list
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *date *: *(\d+ \w+ \d+)/i) {
    $date = $1;
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *scribe(?:nick)? *-:? *$/i) {
    delete $curscribes{fc $records[$i]->{speaker}}; # Remove speaker as scribe
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *scribe(?:nick)? *\+:? *$/i) {
    my $s = $records[$i]->{speaker};
    $curscribes{fc $s} = 1;		# Add speaker as scribe
    $scribes{fc $s} = $s if !$scribes{fc $s}; # Add to collected names
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *scribe(?:nick)? *: *$/i) {
    push(@diagnostics, "Ignored empty command \"$records[$i]->{text}\"");

  } elsif ($records[$i]->{text} =~
	   /^ *scribe(?:nick)? *(:|\+:?) *($scribepat(?:, *$scribepat)*)$/i) {
    %curscribes = () if $1 eq ':';	# Reset scribe nicks
    foreach (split(/ *, */, $2)) {	# Split at commas
      /^$scribepat$/;			# Split into nick and name
      if ($2) {$scribes{fc $1} = $2}	# Add real name to scribe list
      elsif (!$scribes{fc $1}) {$scribes{fc $1} = $1} # Add nick if no name yet
      $curscribes{fc $1} = 1;		# Add to current scribe nicks
    }
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *scribe *: *([^ ].*?) *$/i) {
    # Probably an old-fashioned scribe command without a nick
    $scribes{fc $1} = $1;		# Add to collected scribe list
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($records[$i]->{text} =~ /^ *scribe(?:nick)? *-:? *([^ ].*)? *$/i) {
    foreach (split(/ *, */, $1)) {delete $curscribes{fc $1} if /^([^ ]+)/}
    $records[$i]->{type} = 'o';		# Omit line from output

 } elsif ($use_zakim && $records[$i]->{speaker} eq 'Zakim' &&
	   $records[$i]->{text} =~ /^agendum \d+\. "(.*)" taken up/) {
    $records[$i]->{type} = 't';		# Mark as topic line
    $records[$i]->{text} = $1;
    $records[$i]->{id} = ++$id;		# Unique ID

  } elsif ($use_zakim && $records[$i]->{speaker} eq 'Zakim' &&
	   $records[$i]->{text} =~ /the attendees (?:were|have been) (.*?),?$/){
    $present{fc $_} = $_ foreach split(/, */, $1);
    $records[$i]->{type} = 'o';		# Omit line from output

  } elsif ($use_zakim && $records[$i]->{speaker} eq 'Zakim' &&
	   $records[$i]->{text} =~ /^\.\.\. (.*?),?$/) {
    my $s = $1;				# See what this is a continuation of
    my $j = $i - 1;
    $j-- while $j >= 0 && ($records[$j]->{text} =~ /^\.\.\. / ||
			   $records[$j]->{speaker} ne 'Zakim');
    if ($j >= 0 && $records[$j]->{text} =~ /the attendees (?:were|have been) /){
      $present{fc $_} = $_ foreach split(/, */, $s);
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

  } elsif ($records[$i]->{text} =~
	   /^ *trackbot *, *(?:(?:dis)?associate|bye|start|end|status)\b/i) {
    $records[$i]->{type} = 'o';		# Ignore some commands to trackbot

  } elsif ($records[$i]->{speaker} eq 'trackbot' &&
	   $records[$i]->{text} =~ /^([a-zA-Z]+-[0-9]+) -- (.*)$/) {
    $records[$i]->{type} = 'B';		# A structured response from trackbot
    $records[$i]->{id} = $2;
    $records[$i]->{text} = $1;

  } elsif ($records[$i]->{speaker} eq 'trackbot' &&
	   $records[$i]->{text} =~ /^$urlpat$/) {
    my $j = $i - 1;			# A URL response from trackbot
    $j-- while $j >= 0 && ($records[$j]->{type} eq 'o' ||
			   $records[$j]->{speaker} ne 'trackbot');
    if ($j < 0) {			# URL belongs to nothing?
      $records[$i]->{type} = 'b';
    } else {				# Make previous line into a link
      $records[$j]->{text} = '->'.$records[$i]->{text}.' '.$records[$j]->{text};
      $records[$i]->{type} = 'o';
    }

  } elsif ($records[$i]->{speaker} eq 'trackbot') {
    $records[$i]->{type} = 'b'		# A response from trackbot

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
	   ($records[$i]->{text} =~ /^($speakerpat) *: *(.*)$/ ||
	    (!$spacecont && $records[$i]->{text}
	     =~ /^ *($speakerpat) *: *(.*)$/)) &&
	   $records[$i]->{type} ne 'c' &&	    # ... and not a failed s///
	   $records[$i]->{text} !~ /^ *$urlpat/i && # ... and not a URL
	   $records[$i]->{text} !~ /^ *$specialpat *:/i) { # ... nor special
    # A speaker line
    $records[$i]->{type} = 's';		# Mark as scribe line
    $lastspeaker{$records[$i]->{speaker}} = $1; # For any continuation lines
    $records[$i]->{speaker} = $1;
    $records[$i]->{text} = $2;
    $speakers{fc $1} = ++$speakerid if !exists $speakers{fc $1};

  } elsif (is_cur_scribe($records[$i]->{speaker}, \%curscribes) &&
	   defined $lastspeaker{$records[$i]->{speaker}} &&
	   ($records[$i]->{text} =~ /^ *(?:\.\.\.*|…) *(.*?) *$/ ||
	    ($implicitcont && $records[$i]->{text} =~ /^ *(.*?) *$/) ||
	    ($spacecont && $records[$i]->{text} =~ /^ +(.*?) *$/)) &&
	   $records[$i]->{type} ne 'c') { # ... and not a failed s///
    # Looks like a continuation line
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

  } elsif ($records[$i]->{text} =~ /^ *(?:\.\.\.*|…) *(.*?) *$/) {
    # Is this a continuation of an action/resolution/issue/topic?
    my ($s, $j, $speaker) = ($1, $i - 1, $records[$i]->{speaker});
    $j-- while $j > 0 && ($records[$j]->{type} eq 'o' ||
			  $records[$j]->{speaker} ne $speaker);
    if ($j >= 0 && $records[$j]->{type} =~ /[artuUd]/) {
      $records[$j]->{text} .= "\t" . $s;
      $records[$i]->{type} = 'o';	# Omit this line from output
    } elsif (is_cur_scribe($speaker, \%curscribes)) {
      # Not a continuation of anything, but it is by the scribe.
      $records[$i]->{type} = 'd';		# Mark as descriptive text
      $lastspeaker{$records[$i]->{speaker}} = undef; # No continuation expected
    }

  } elsif (is_cur_scribe($records[$i]->{speaker}, \%curscribes) &&
  	   $records[$i]->{type} eq 'c') {
    # It's a failed s/// command by the speaker. Leave it as a 'c'.

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

# Add a list of speakers that do not appear in %present, if any.
my @also = grep !exists($present{fc $_}),
    fc_uniq(map $_->{speaker}, grep $_->{type} eq 's', @records);
push @diagnostics, "Maybe present: " .
    join(", ", sort {fc($a) cmp fc($b)} @also) if @also;

# Step 6. Convert records to HTML and then fill a template.
#
# Each type of record is converted to a specific HTML fragment, with
# %1$s replaced by the speaker, %2$s by the ID and %3$s by the text.
#
# Also replace \t (i.e., placeholders for line breaks) as appropriate.
#
my %linepat = (
  a => "<p class=action id=%2\$s><strong>Action:</strong> %3\$s</p>\n",
  b => "<p class=bot><cite>&lt;%1\$s&gt;</cite> %3\$s</p>\n",
  B => "<p class=bot><cite>&lt;%1\$s&gt;</cite> <strong>%3\$s:</strong> %2\$s</p>\n",
  d => "<p class=summary>%3\$s</p>\n",
  i => $scribeonly ? '' : "<p class=irc><cite>&lt;%1\$s&gt;</cite> %3\$s</p>\n",
  c => $scribeonly ? '' : "<p class=irc><cite>&lt;%1\$s&gt;</cite> %3\$s</p>\n",
  o => '',
  r => "<p class=resolution id=%2\$s><strong>Resolution:</strong> %3\$s</p>\n",
  s => "<p class=\"phone %4\$s\"><cite>%1\$s:</cite> %3\$s</p>\n",
  n => "<p class=anchor id=\"%2\$s\"><a href=\"#%2\$s\">⚓</a></p>\n",
  u => "<p class=issue id=%2\$s><strong>Issue:</strong> %3\$s</p>\n",
  t => "</section>\n\n<section>\n<h3 id=%2\$s>%3\$s</h3>\n");

my $minutes = '';
foreach my $p (@records) {
  # The last part generates nothing, but avoids warnings for unused args.
  my $line = sprintf $linepat{$p->{type}} . '%1$.0s%2$.0s%3$.0s%4$.0s',
    esc($p->{speaker}), $p->{id}, esc($p->{text}, $emphasis, 1, 1),
    $speakers{fc $p->{speaker}} // '';
  if ($keeplines) {$line =~ s/\t/<br>\n… /g;} else {$line =~ tr/\t/ /;}
  $minutes .= $line;
}

# @stylesheets is an array of triples [alt, title, url], where alt = 0
# means this is the default style, not 0 means an "alternate" style.
#
my $alt = 0;
my $w3 = 'https://www.w3.org';
my @stylesheets = ();
push @stylesheets, [$alt++, "Default", $stylesheet] if defined $stylesheet;
if ($styleset eq 'team') {
  push @stylesheets,
      [$alt + $old_style, "2018", "$w3/StyleSheets/scribe2/team.css"],
      [$alt + !$old_style, "2004", "$w3/StyleSheets/base.css"],
      [$alt + !$old_style, "2004", "$w3/StyleSheets/team.css"],
      [$alt + !$old_style, "2004", "$w3/StyleSheets/team-minutes.css"],
      [$alt + !$old_style, "2004", "$w3/2004/02/minutes-style.css"],
      [1, "Typewriter", "$w3/StyleSheets/scribe2/tt-team.css"];
} elsif ($styleset eq 'member') {
  push @stylesheets,
      [$alt + $old_style, "2018", "$w3/StyleSheets/scribe2/member.css"],
      [$alt + !$old_style, "2004", "$w3/StyleSheets/base.css"],
      [$alt + !$old_style, "2004", "$w3/StyleSheets/member.css"],
      [$alt + !$old_style, "2004", "$w3/StyleSheets/member-minutes.css"],
      [$alt + !$old_style, "2004", "$w3/2004/02/minutes-style.css"],
      [1, "Typewriter", "$w3/StyleSheets/scribe2/tt-member.css"];
} else {			# 'public' or 'fancy'
  my $f = $styleset eq 'fancy';
  push @stylesheets,
      [$alt + $old_style + $f, "2018", "$w3/StyleSheets/scribe2/public.css"],
      [$alt + !$old_style + $f, "2004", "$w3/StyleSheets/base.css"],
      [$alt + !$old_style + $f, "2004", "$w3/StyleSheets/public.css"],
      [$alt + !$old_style + $f, "2004", "$w3/2004/02/minutes-style.css"],
      [$alt + !$f, "Fancy", "$w3/StyleSheets/scribe2/fancy.css"],
      [1, "Typewriter", "$w3/StyleSheets/scribe2/tt-member.css"];
}

# Format some of the variables used in the template below
#
my $style = join("\n",
  map {"<link rel=\"" . ($_->[0] ? "alternate " : "") . "stylesheet\" " .
    "type=\"text/css\" title=\"$_->[1]\" href=\"$_->[2]\">"} @stylesheets);

$logo = "<p>$logo</p>\n\n" if defined $logo && $logo ne '';
$logo = '' if !defined $logo && ($styleset eq 'fancy');
$logo = "<p>$w3clogo</p>\n\n" if !defined $logo;
my $draft = $final ? "" : "&ndash; DRAFT &ndash;<br>\n";
my $log = defined $logging_url?"<a href=\"$logging_url\">$irclog_icon</a>\n":"";
my $present = esc(join(", ", map($present{$_}, sort keys %present))) || '-';
my $regrets = esc(join(", ", map($regrets{$_}, sort keys %regrets))) || '-';
my $scribes = esc(join(", ", sort {fc($a) cmp fc($b)} values %scribes)) || '-';
my $chairs = esc(join(", ", sort {fc($a) cmp fc($b)} values %chairs)) || '-';
my $diagnostics = !$embed_diagnostics || !@diagnostics ? "" :
  "<div class=diagnostics>\n<h2>Diagnostics<\/h2>\n" .
  join("", map {"<p class=warning>" . esc($_) . "</p>\n"} @diagnostics) .
  "</div>\n";

# Collect lists of actions, resolutions and issues from the @records.
# Wrap each list in a <div> and add a corresponding item in the ToC
# (unless the list is empty).
#
my $actions = join("",
		   map("<li><a href=\"#" . $_->{id} . "\">" .
		       esc($_->{text}, $emphasis, -1, 1) . "</a></li>\n",
		       grep($_->{type} eq 'a', @records)));
my $actiontoc = !$actions ? '' :
    "<li><a href=\"#ActionSummary\">Summary of action items</a></li>\n";
$actions = "\n<div id=ActionSummary>\n<h2>Summary of action items</h2>
<ol>\n$actions</ol>\n</div>\n" if $actions;
if ($keeplines) {$actions =~ s/\t/<br>\n… /g;} else {$actions =~ tr/\t/ /;}

my $resolutions = join("",
		       map("<li><a href=\"#" . $_->{id} . "\">" .
			   esc($_->{text}, $emphasis, -1, 1) . "</a></li>\n",
			   grep($_->{type} eq 'r', @records)));
my $resolutiontoc = !$resolutions ? '' :
    "<li><a href=\"#ResolutionSummary\">Summary of resolutions</a></li>\n";
$resolutions = "\n<div id=ResolutionSummary>\n<h2>Summary of resolutions</h2>
<ol>\n$resolutions</ol>\n</div>\n" if $resolutions;
if ($keeplines) {$resolutions =~ s/\t/<br>\n… /g;} else {$resolutions =~ tr/\t/ /;}

my $issues = join("",
		  map("<li><a href=\"#" . $_->{id} . "\">" .
		      esc($_->{text}, $emphasis, -1, 1) . "</a></li>\n",
		      grep($_->{type} eq 'u', @records)));
my $issuetoc = !$issues ? '' :
    "<li><a href=\"#IssueSummary\">Summary of issues</a></li>\n";
$issues = "\n<div id=IssueSummary>\n<h2>Summary of issues</h2>
<ol>\n$issues</ol>\n</div>\n" if $issues;
if ($keeplines) {$issues =~ s/\t/<br>\n… /g;} else {$issues =~ tr/\t/ /;}

# Collect topics (records with type 't') for the ToC.
#
my $topics = join("",
		  map("<li><a href=\"#" . $_->{id} . "\">" .
		      esc($_->{text}, $emphasis, -1, 1) . "</a></li>\n",
		      grep($_->{type} eq 't', @records)));
if ($keeplines) {$topics =~ s/\t/<br>\n… /g;} else {$topics =~ tr/\t/ /;}

# And output the formatted HTML.
#
print "<!DOCTYPE html>
<html lang=en>
<head>
<meta charset=utf-8>
<title>$meeting &ndash; $date</title>
<meta name=viewport content=\"width=device-width\">
$style
</head>

<body>
<header>
$logo<h1>$draft$meeting</h1>
<h2>$date</h2>

<nav id=links>
$prev_meeting$agenda$log$next_meeting</nav>
</header>

<div id=prelims>
<div id=attendees>
<h2>Attendees</h2>
<dl class=intro>
<dt>Present</dt><dd>$present</dd>
<dt>Regrets</dt><dd>$regrets</dd>
<dt>Chair</dt><dd>$chairs</dd>
<dt>Scribe</dt><dd>$scribes</dd>
</dl>
</div>

<nav id=toc>
<h2>Contents</h2>
<ul>
<li><a href=\"#meeting\">Meeting minutes</a>
<ol>
$topics</ol>
</li>
$actiontoc$resolutiontoc$issuetoc</ul>
</nav>
</div>

<main id=meeting class=meeting>
<h2>Meeting minutes</h2>
<section>$minutes</section>
</main>
$actions$resolutions$issues

<address>Minutes manually created (not a transcript), formatted by <a
href=\"https://w3c.github.io/scribe2/scribedoc.html\"
>scribe.perl</a> version $revision ($versiondate).</a></address>

$diagnostics</body>
</html>
";

print STDERR map("* $_\n", @diagnostics) if !$embed_diagnostics;

__END__

=head1 NAME

scribe.perl - Turn an IRC log of a meeting into minutes in HTML

=head1 SYNOPSIS

scribe.perl [options] [file ...]

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
  --minutes=URL		Used to guess a date if the URL contains YYYY/MM/DD
  --logo=markup		Replace the W3C link and logo with this HTML markup
  --nologo      	Same as --logo=""
  --stylesheet=URL	Use this style sheet instead of the default

You can use single dash (-) or double (--). Options are
case-insensitive and can be abbreviated. Some options can be negated
with `no' (e.g., --nokeeplines). For the full manual see
L<https://w3c.github.io/scribe2/scribedoc.html>
