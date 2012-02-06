#!/usr/bin/perl
#######################################################################
# Copyright (c) 2010 Grégory Duchatelet <skygreg@gmail.com>
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
# http://www.apache.org/licenses/LICENSE-2.0
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License. 
# 
#######################################################################
# mysql_msr.pl - Multiple Source Replication
# 
# This script add the ability to a running MySQL slave, to replicate
# from many masters.
# WARNING: each masters MUST have different databases.
# It is not as safe and fast as the official MySQL worklog :
# http://forge.mysql.com/worklog/task.php?id=1697
# and has less features, but it simply works ...
# The main feature is to replicate in parallel.
#
# Grants: you need a mysql user with ALL privileges, GRANT OPTION, and SUPER
# GRANT ALL PRIVILEGES ON *.* TO 'msruser'@'10.0.%' IDENTIFIED BY 'the_complex_password' WITH GRANT OPTION;
# GRANT SUPER ON *.* TO 'msruser'@'10.0.%';
# 
# Typical (and tested) configuration:
# this script is running on the destination server (which could be the slave),
# the slave is configured to replicate "main" datas from "main master",
# a management database is need, by default named "msr",
# on this database you configure masters to replicate from, with eventually greylisting.
# Greylist = which databases to replicate, or which to not replicate.
# Filtering is done only on database, not tables.
#
#######################################################################


#######################################################################
## External Libraries
#######################################################################
# Instead, it would be good to use PAR or App::FatPacker.
#
use strict;
use warnings FATAL => 'all';


# {{{ Log::Funlog - Log module with fun inside!
# Author: Gabriel Guillon, from Cashew team
# From http://search.cpan.org/~korsani/Log-Funlog-0.87/lib/Log/Funlog.pm

package Log::Funlog;
use Carp;
use strict;
use File::Basename;
use IO::Handle;
use Fcntl qw(:flock);

BEGIN {
	use Exporter;
	our ($VERSION, @ISA, @EXPORT, @EXPORT_OK );
	@ISA=qw(Exporter);
	@EXPORT=qw( );
	@EXPORT_OK=qw( &error $VERBOSE $LEVELMAX $VERSION );
	$VERSION='0.99';
	sub VERSION {
		(my $me, my $askedver)=@_;
		$VERSION=~s/(.*)_\d+/$1/;
		croak "Please update: $me is version $VERSION and you asked version $askedver" if ($VERSION < $askedver);
	}
}
my @fun;
our %funlog_args;
eval 'use Log::Funlog::Lang 0.3';
if ($@) {
	@fun=();
} else {
	@fun=@{ (Log::Funlog::Lang->new())[1] };
}
#use Sys::Syslog;
my $count=0;
use vars qw( %funlog_args $me $error_header $error $metaheader);

# Defined here, used later!
#####################################
my $rexpleft=q/<>{}()[]/;				#Regular expression that are supposed to be on the left of the thing to print
my $rexprite=$rexpleft;
$rexprite=~tr/><}{)(][/<>{}()[]/;		#tr same for right
my $rexpsym=q'+-=|!.\/';		#These can by anywhere (left or right)
$rexpleft=quotemeta $rexpleft;
$rexprite=quotemeta $rexprite;
$rexpsym=quotemeta $rexpsym;
my $level;
my $LOCK_SH=1;
my $LOCK_EX=2;
my $LOCK_NB=4;
my $LOCK_UN=8;
my $handleout;			#Handle of the output
my %whattoprint;
my %colortable=(
	'black' => "\e[30;1m",
	'red' => "\e[31;1m",
	'green' => "\e[32;1m",
	'yellow' => "\e[33;1m",
	'blue' => "\e[34;1m",
	'magenta' => "\e[35;1m",
	'cyan' => "\e[36;1m",
	'white' => "\e[37;1m",
	'none' => "\e[0m"
);
my %defaultcolors=(
	'level' => $colortable{'red'},
	'caller' => $colortable{'none'},
	'date' => $colortable{'none'},
	'prog' => $colortable{'magenta'},
	'error' => $colortable{'red'},
	'msg' => $colortable{'yellow'}
);
my @authorized_level_types=('numeric','sequential');		#Level types
my %colors;		#will contain the printed colors. It is the same than %defaultcolors, but probably different :)
our $hadnocr=0;		#Remember if previous call had $nocr (to print header at first call with $nocr, but not further)

################################################################################################################################
sub replace {						#replace things like %l<-->l by things like <-** ->
	my $header=shift;
	my $what=shift;
	my $center=shift;
	if ($center) {
		$header=~s/\%$what$what/$center/;				# for cases like %dd
		#
		# Now, for complicated cases like %d<-->d or %d-<>-d
		# 
		$header=~s/\%$what(.*[$rexpleft]+)([$rexprite]+.*)$what/$1$center$2/;	#%d-<>-d   -> -<plop>-
											#%d<-->d   -> <-->
		$header=~s/\%$what(.*[$rexpsym]+)([$rexpsym]+.*)$what/$1$center$2/;	#-<plop>-  -> -<plop>-
											#<-->      -> <-plop->
	} else {
		$header=~s/\%$what.*$what//;
	}
	return $header;
}

################################################################################################################################
################################################################################################################################
sub new {
	my $this = shift;
	my $class = ref($this) || $this;
	%funlog_args=@_;							#getting funlog_args to a hash
	
	# Okay, now sanity checking!
	# This is cool because we have time, so we can do all kind of checking, calculating, things like that
	#########################################
	if (defined $funlog_args{daemon} and $funlog_args{daemon}) {
		croak 'You want me to be a daemon, but you didn\'t specifie a file to log to...' unless (defined $funlog_args{file});
	}
	croak "'verbose' option is mandatory." if (! $funlog_args{'verbose'});
	croak "'verbose' should be of the form n/m or max/m" if (($funlog_args{'verbose'} !~ /^\d+\/\d+$/) and ($funlog_args{'verbose'} !~ /^[mM][aA][xX]\/\d+$/));

	# Parsing 'ltype' option
	#########################################
	if (defined $funlog_args{ltype}) {
		if (! grep(/$funlog_args{ltype}/,@authorized_level_types)) {
			croak "Unknow ltype '$funlog_args{ltype}'";
		}
	} else {
		$funlog_args{ltype}='sequential';
	}

	# Parsing 'verbose' option...
	#########################################
	my ($verbose,$levelmax)=split('/',$funlog_args{verbose});
	$levelmax=$levelmax ? $levelmax : "";						#in case it is not defined...
	$verbose=$levelmax if ($verbose =~ /^[mM][aA][xX]$/);
	if (($verbose !~ /\d+/) or ($levelmax !~ /\d+/)) {
		carp "Arguments in 'verbose' should be of the form n/m, where n and m are numerics.\nAs this is a new feature, I'll assume you didn't upgraded your script so I'll make it compatible...\nAnyhow, consider upgrading soon!\n";
		croak "No 'levelmax' provided" unless ($funlog_args{levelmax});
	} else {
		$funlog_args{verbose}=$verbose;
		$funlog_args{levelmax}=$levelmax;
	}
	if ($funlog_args{verbose} > $funlog_args{levelmax}) {
		carp "You ask verbose $funlog_args{verbose} and the max is $funlog_args{levelmax}. I set your verbose at $funlog_args{levelmax}.\n";
		$funlog_args{verbose}=$funlog_args{levelmax};
	}


	# Time for fun!
	#########################################
	if (defined $funlog_args{fun}) {
		croak "'fun' should only be a number (between 0 and 100, bounds excluded)." if ($funlog_args{fun} !~ /^\d+$/);
		croak "0<fun<=100" if ($funlog_args{fun}>100 or $funlog_args{fun}<=0);
		croak "You want fun but Log::Funlog::Lang is not available, or is too old." if ($#fun <= 0);
	}

	# Colors
	#########################################
	#We will build %colors here.
	#If color is wanted:
	#	if default is wanted, %colors = %defaultcolors
	#	if not, %colors = %defaultcolors, overriden by the parameters provided
	#If no colors is wanted, %colors will be filled with the 'none' colors.
	#
	#This way of doing should be quicker :)
	#
	if (exists $funlog_args{'colors'} and $funlog_args{'colors'} ) {							#If color is wanted
		use Config;
		if ($Config{'osname'} eq 'MSWin32') {				#Oh oh!
			carp 'Colors wanted, but MSwin detected. Colors deactivated (because not implemented yet)';
			delete $funlog_args{'colors'};
			$colortable{'none'}='';							#putting 'none' color to void
			foreach my $color (keys %defaultcolors) {
				$colors{$color}=$colortable{'none'};		#and propagating it
			}
#			no Config;
		} else {											#We are not in MSWin...
			if (ref(\$funlog_args{'colors'}) eq 'SCALAR') {		#default colors?	
				%colors=%defaultcolors if ($funlog_args{'colors'});
			} elsif(ref($funlog_args{'colors'}) eq 'HASH') {		#No... Overridden colors :)
				foreach my $item (keys %defaultcolors) {
					$colors{$item}=exists ${		#If the color is provided
						$funlog_args{'colors'}
					}{$item}?
					$colortable{
						${
							$funlog_args{'colors'}		#we take it
						}{$item}
					}:$defaultcolors{$item};		#if not, we take the default one
				}
			} else {
				croak("'colors' must be type of SCALAR or HASH, not ".ref($funlog_args{'colors'})."\n");
			}
		}
	} else {										#no colors? so the color table will contain the color 'none'
		$colortable{'none'}='';						#Avoid printing "\e[0m" :)
		foreach my $item (keys %defaultcolors) {
			$colors{$item}=$colortable{'none'};
		}
	}


# Error handler
#########################################
	$error_header=defined $funlog_args{error_header} ? $funlog_args{error_header} : '## Oops! ##';

# We define default cosmetic if no one was defined
#########################################
	if (not defined $funlog_args{cosmetic}) {
		$funlog_args{'cosmetic'}='x';
	} elsif ($funlog_args{'cosmetic'} !~ /^[[:^cntrl:]]$/) {
		croak("'cosmetic' must be one character long, and printable.");
	}

# Parsing header. Goal is to avoid work in the wr() function
#########################################
	if (defined $funlog_args{header}) {

		$metaheader=$funlog_args{header};

		# if %ll is present, we can be sure that it will always be, but it will vary so we replace by a variable
		if ($metaheader=~/\%l.*l/) {
			$whattoprint{'l'}=1;
			$metaheader=replace($metaheader,"l","\$level");
		}

		# same for %dd
		$whattoprint{'d'}=1 if ($metaheader=~/\%d.*d/);
		$metaheader=replace($metaheader,"d",$colors{'date'}."\$date".$colortable{'none'});

		# but %pp won't vary
		$me=basename("$0");
		chomp $me;
		$whattoprint{'p'}=1 if ($metaheader=~/\%p.*p/);
		$metaheader=replace($metaheader,"p",$colors{'prog'}.$me.$colortable{'none'});
		# and stack will be present or not, depending of the state of the stack
		$whattoprint{'s'}=1 if ($metaheader=~/\%s.*s/);

		if ((! defined $funlog_args{'caller'}) and ($metaheader=~/\%s.*s/)) {
			carp "\%ss is defined but 'caller' option is not specified.\nI assume 'caller => 1'";
			$funlog_args{'caller'}=1;
		}
	} else {
		$metaheader="";
	}

# Daemon. We calculate here the output handle to use
##########################################
	if ($funlog_args{'daemon'}) {
		open($handleout,">>$funlog_args{'file'}") or croak "$!";
	} else {
		$handleout=\*STDERR;
	}
	$handleout->autoflush(1);
# -n handling
##########################################
	$funlog_args{'-n'}='-n' unless $funlog_args{'-n'};

##########################################
# End of parsing
##########################################

	my $self = \&wr;
	bless $self, $class;			#The function's address is now a Log::Funlog object
	return $self;				#Return the function's address, that is an object Log::Funlog
}

########################################################################################
########################################################################################
# This is the main function
########################################################################################
########################################################################################
sub wr {
	my $self=shift;
	my $level=shift;						#log level wanted by the user
	return if ($level > $funlog_args{verbose} or $level == 0);	#and exit if it is greater than the verbosity

	my $return_code;
	my $nocr;
	my $l = '';

# Header building!!
#####################################
	if ($_[0] eq $funlog_args{'-n'}) {
		shift;
		$nocr=1;
	} else {
		$nocr=0;
	};
	if ($metaheader and not $hadnocr) {							#Hey hey! Won't calculate anything if there is nothing to print!
		my $header=$metaheader;
		if ($whattoprint{'s'}) {						#if the user want to print the call stack
			my $caller;
			if (($funlog_args{'caller'} =~ /^last$/) or ($funlog_args{'caller'} =~ /^1$/)) {
				$caller=(caller($error?2:1))[3];
			} else {						#okay... I will have to unstack all the calls to an array...
				my @stack;
				my $i=1;
				while (my $tmp=(caller($error?$i+1:$i))[3]) {	#turn as long as there is something on the stack
					push @stack,($tmp);
					$i++;
				};
				@stack=reverse @stack;
				if ($funlog_args{'caller'} eq "all") {;					#all the calls
					$caller=join(':',@stack);
				} else {
					if ($#stack >= 0) {
						my $num=$funlog_args{'caller'};
						$num=$#stack if ($num>=$#stack);		#in case the stack is greater that the number of call we want to print
						if ($funlog_args{'caller'} eq "all") {							#all the cals
							$caller=join(':',@stack);
						} elsif ($funlog_args{'caller'} =~ /^-\d+$/) {					#the n first calls
							$caller=join(':',splice(@stack,0,-$num));
						} elsif ($funlog_args{'caller'} =~ /^\d+$/) {					#just the n last calls
							$caller=join(':',splice(@stack,1+$#stack-$num));
						}
					}
				}
			}

			if ($caller) {							#if there were something on the stack (ie: we are not in 'main')
				$caller =~ s/mysql_msr::main:(mysql_msr)?:*//g;
				$caller =~ s/\:*?(_\w)?\:*Log:*.*//g;
				my @a=split(/\//,$caller);			#split..
				@a=reverse @a;						#reverse...
				$header=replace($header,"s",$colors{'caller'}.join(':',@a).$colortable{'none'});
			} else {
				$header=replace($header,"s");
			}
		} else {
			$header=replace($header,"s");
		}
		if ($whattoprint{'d'}) {
			my $tmp=scalar localtime;
			$header=~s/\$date/$tmp/;
		}
		if ($whattoprint{'l'}) {
			my $tmp;
			if ($funlog_args{ltype} eq 'numeric') {
				$tmp=$colors{'level'}.$level.$colortable{'none'};
			} elsif ($funlog_args{ltype} eq 'sequential') {
				$tmp=$colors{'level'}.$funlog_args{cosmetic} x $level. " " x ($funlog_args{levelmax} - $level).$colortable{'none'};	# [xx  ]
			}
			$header=~s/\$level/$tmp/;
		}

		#####################################
		#	End of header building
		#####################################
		$l .= $header;						#print the header
	}
	if ($error)
	{
		$l .= $colors{'error'};
	}
	else
	{
		$l .= $colors{'msg'};
	}
	while (my $tolog=shift) {			#and then print all the things the user wants me to print
		$l .= $tolog;
		$return_code.=$tolog;
	}
	$l .= $colortable{'none'};
	$l .= $/ unless $nocr;
	#Passe le fun autour de toi!
	$l .= $fun[1+int(rand $#fun)].$/ if ($funlog_args{fun} and (rand(100)<$funlog_args{fun}) and ($count>10));			#write a bit of fun, but not in the first 10 lines
	#$l .= "nc:$nocr\n";
	$count++;
	if ($nocr) {
		$hadnocr=1;
	} else {
		$hadnocr=0;
	}
	#$l .= "hnc:$hadnocr\n";

	flock($handleout, LOCK_EX) or warn $!;
	print { $handleout } $l;
	unless ($nocr)
	{
		flock($handleout, LOCK_UN) or warn $!;
	}
	return $return_code;
}
sub error {
	my $self=shift;
	$error=1;
	#my $ec=$self->wr(1,$error_header," ",@_);
	my $ec=$self->wr(1,@_);
	$error=0;
	return $ec;
}
1; # }}}



#######################################################################
## Internal Libraries
#######################################################################

# 
# Log : mixed Singleton and Exporting patterns
# for a logger class.
#
package Log; # {{{
use strict;
use warnings FATAL => 'all';
use English qw(-no_match_vars);
use Carp;
use Exporter;
our @ISA = qw(Exporter);
our @EXPORT = qw( _l _d _i _dump _err);

my $singleton;

sub new
{
	my ( $class, @args ) = @_;
	return $singleton if(defined($singleton));
	
	my $self = {
		'logger' => new Log::Funlog(@args),
	};
	bless $self, $class;
	$singleton = $self;
}

sub _l
{
	my (@s) = @_;
	unless(defined($singleton))
	{
		croak "You need to initialize Log before.";
	}
	$singleton->{logger}->wr(@s);
}

sub _d 
{
	return _l(5, @_);
	my ($package, undef, $line) = caller 1;
	@_ = map { (my $temp = $_) =~ s/\n/\n# /g; $temp; }
		map { defined $_ ? $_ : 'undef' }
		@_;
	_l(5, "# $package:$line $PID ", join(' ', @_));
}

# info
sub _i
{
	_l(1, @_);
}

# error
sub _err
{
	$singleton->{logger}->error(@_);
}

sub _dump
{
	use Data::Dumper;
	warn Dumper(\@_);
}


1; # }}}

#
# Can read INI files, Zend compatible (inheritance)
#
package ConfigIni; # {{{
use strict;
use warnings FATAL => 'all';
use English qw(-no_match_vars);
require Exporter;
our @ISA = qw(Exporter);
our %EXPORT_TAGS = (
	'all' => [ qw( parse_ini  get_all) ],
);

our @EXPORT_OK = ( @{ $EXPORT_TAGS{'all'} } );

use Data::Dumper;

# regexp de matching d'un nom de section
my $reg_section = '[a-zA-Z0-9_-]+';
# regexp de matching un nom de variable
my $reg_prop = '[a-zA-Z0-9_.-]+';

# ref sur un hash des sections découvertes
my $sections;

# parse_ini($nom_fichier_ini, $nom_section)
sub parse_ini
{
	my $file = shift;
	my $section_match = shift || '';

	my $fh;
	my $l;

	my $sec_name = '';
	my $accumulator = '';

	unless (open $fh, "<$file")
	{
		die "Cannot read INI file $file: $!\n";
	}
	while($l = <$fh>)
	{
		# match value multiligne suivante
		if($accumulator ne '' && $l =~ /^[^"]+$/)
		{
			#print "acc multiligne $.\n";
			$accumulator .= $l;
			next;
		}

		# match value multiligne suivante
		if($accumulator ne '' && $l =~ /"$/)
		{
			#print "\e[44;mFIN\e[0m multiligne $.\n";
			$l = $accumulator.$l;
			$accumulator = '';
			#print "redo l\n";
			# chomp DOS UNIX
			$l =~ s/\r\n?$//;
			redo;
		}

		# comment
		next if $l =~ /^(;|\s*$)/;
		# chomp DOS UNIX
		$l =~ s/\r\n?$//;

		# section
		if($l =~ /^\[([^\]]+)\]/)
		{
			$sec_name = $1;
			#print "section=$sec_name\n";

			# trim
			$sec_name =~ s/^\s*//;
			$sec_name =~ s/\s*$//;
			my $regexp = $reg_section;
			if($sec_name =~ /($regexp)\s*:\s*($regexp)/)
			{
				$sec_name = $1;
				my $parent = $2;
				#print "heritage = $sec_name <= $parent\n";

				if($sections->{$parent})
				{
					#print "copy $parent\n";
					# Dump() met la string a évaluer. en mode use strict eval refuse silencieusement d'importer la
					# variable $VAR1 générée par la fonction si on ne la nomme pas.
					my $str =  Data::Dumper->Dump([$sections->{$parent}], ['$sections->{$sec_name}']);
					#print "str=$str\n";

                    eval $str;

					#print Dumper($sections->{$sec_name});
				}
			}
			else
			{
				$sections->{$sec_name} = {};
			}

			next;
		}

		# value, simple ligne
		if($l =~ /\s*($reg_prop)\s*=\s*([^" ].*|"[^"]*")/)
		{
			my $var = $1;
			my $value = $2;

			# traitement de $value quoted
			if($value =~ /^"/)
			{
				$value =~ s/(^"|"$)//g;
			}

			$value =~ s/&gt;/>/g;
			$value =~ s/&lt;/</g;
			$value =~ s/&amp;/&/g;
			$value =~ s/&quote;/"/g;

			# print "$var AFFECT <$value>\n";

			# parcours de chemin du nom de la variable splité sur les .
			# assignation dans le HASH global $sections
			my @val_key = split(/\./, $var);
			my $nb;
			if(($nb = scalar(@val_key)) > 1)
			{
				# CAS 1 : avec nom de clé imbriquée : moi.toi = val
				# print "split '@val_key'\n'";

				# parcours le HASH et crée les clés parents
				my $href = $sections->{$sec_name};
				for(my $i = 0; $i < $nb - 1; $i++)
				{
					my $k = $val_key[$i];
					if(!$href->{$k})
					{
						$href->{$k} = {};
					}
					$href = $href->{$k};
				}

				# insere la valeur à la bonne place
				$href->{$val_key[-1]} = $value;
			}
			else
			{
				# CAS 2 : nom de clé simple : var = val
				$sections->{$sec_name}->{$var} = $value;
			}

			next;
		}

		# match value multiligne
		if($l =~ /\s*($reg_prop)\s*=\s*("[^"]+$)/)
		{
			#print "début multiligne $.:'$l'\n";
			$accumulator = $l;
			next;
		}

		print "\e[41;37;1mparse error\e[0m:$.:$l\n";
	}

	close $fh;

	if($section_match eq '')
	{
		return $sections;
	}
	else
	{
		return $sections->{$section_match};
	}
}

sub get_all { $sections; }

1; # }}}

#
# A binlog event
#
package Binlog; # {{{
use warnings FATAL => 'all';
use Carp;
use English qw(-no_match_vars);
use POSIX qw(setsid floor ceil strftime mktime);
use Carp;
use vars qw($AUTOLOAD);
Log->import();

sub AUTOLOAD
{
	my $self = shift @_;
	my $attr = $AUTOLOAD;
	$attr =~ s/.*:://;
	return unless $attr =~ /[^A-Z]/; # don't overload DESTROY and co
	$attr = lc $attr;
	croak "$attr is not a valid attribut" unless(defined($self->{$attr}));
	$self->{$attr} = shift if @_;
	return $self->{$attr};
}

sub new
{
	my ($class, $binlogfile, $pos, $db, $delimiter_def) = @_;
	$pos = defined($pos) ? $pos : -1;
	$delimiter_def = defined($delimiter_def) ? $delimiter_def : '';
	$db = defined($db) ? $db : '';
	my $self = {
		'pos' => $pos,
		'sql' => [],
		'is_full' => 0,
		'error' => '',
		'next_pos' => 0,
		'binlogfile' => $binlogfile,
		'type' => 'none',
		'is_in_transaction' => 0,
		'is_a_transaction' => 0,
		'delimiter' => ";\n",
		'delimiter_def' => $delimiter_def,
		'date' => 0,
		'db' => $db,
		'version' => 0,
		'tmpsql' => [],
	};
	bless $self, $class;
	$self->set_delimiter_def($self->{delimiter_def});
	return $self;
}


# Benchmarked :
#  use Benchmark qw'cmpthese timethis';
#  my $binlog = new Binlog($slave->{binlogfile});
#  timethis(100000, sub { $binlog->parse("#100708 14:28:01 server id 93  end_log_pos 6428150      Query   thread_id=882981560     exec_time=0     error_code=0\n"); });
#  exit;
# output:
# timethis 100000:  3 wallclock secs ( 2.18 usr +  0.29 sys =  2.47 CPU) @ 40485.83/s (n=100000)
sub parse
{
	my ($self, $line) = @_;
	if($line !~ /^#/)
	{
		my $delimiter = $self->{delimiter};
		chomp($delimiter);
		# Handle transaction added by mysqlbinlog
		if($line =~ /^BEGIN/)
		{
			$self->{is_in_transaction} = 1;
			$self->{is_a_transaction} = 1;
		}
		# COMMIT for a query, END for a function
		elsif($line =~ /^COMMIT/ or $line =~ /^END/)
		{
			$self->{is_in_transaction} = 0;
		}
		# SET INSERT_ID _MUST_ be in the same queries "pack", if not
		# we could accidentaly "rotate" (at the end of a binlog batch) between 
		# SET INSERT_ID and the INSERT concerned by this one.
		elsif(!$self->{is_in_transaction} and $line =~ /^SET INSERT_ID/)
		{
			$self->{is_in_transaction} = 2;
		}
		elsif($self->{is_in_transaction} == 2 and $line =~ qr/^\Q$delimiter/)
		{
			$self->{is_in_transaction} = 0;
		}
		# detecting database
		elsif($line =~ /^use (.+)\/\*!\*\/;/i)
		{
			$self->{db} = $1;
			$self->add($line);
		}
		#
		# SQL 
		#

		if(!$self->{delimiter_def} and $line =~ /^DELIMITER/)
		{
			$self->set_delimiter_def($line);
		}

		$self->add($line);
	}
	elsif($line =~ /^# at (\d+)/)
	{
		$self->set_position($1);
	}
	elsif($line =~ /^#(\d+)\s+(\d+:\d+:\d+)\s+/)
	{
		$self->parse_info($line);
	}
	elsif($line =~ /^# End of log file/)
	{
		#$self->{next_pos} = 0;
		$self->{is_full} = 1;
		unless ($self->is_rotate)
		{
			$self->{type} = 'end' ; # END
		}
	}
	elsif ($line =~ /^ERROR:/ and $line =~ /failed on connect:/i)
	{
		_err("Unable to connect to master ".$self->{name}." (".$self->{host}.":".$self->{port}.")");
		$self->{is_full} = 1;
		$self->{error} = "Unable to connect to master";
	}
	elsif ($line !~ /^##/)
	{
		_d("Not parsed: $line");
	}
}

sub set_delimiter_def
{
	my ($self, $def) = @_;
	if($def =~ /^DELIMITER (.+)/)
	{
		$self->{delimiter} = $1;
		$self->{delimiter_def} = $def;
		$self->{delimiter} .= $/ if (chomp($def));
	}
}

sub add
{
	my ($self, $sql) = @_;
	if($sql =~ m{/\*!\*/;$})
	{
		push @{$self->{sql}}, @{$self->{tmpsql}} if (scalar(@{$self->{tmpsql}}) > 0);
		push @{$self->{sql}}, $sql;
		$self->{tmpsql} = [];
	}
	else
	{
		push @{$self->{tmpsql}}, $sql;
	}
}

sub set_position
{
	my ($self, $pos) = @_;
	$pos = int($pos);
	if($pos >= 0)
	{
		if($self->{pos} == -1)
		{
			$self->{pos} = $pos;
		}
		elsif($self->{pos} == 0)
		{
			$self->{pos} = 4;
		}
		elsif(not $self->{is_in_transaction})
		{
			$self->{next_pos} = $pos;
			$self->{is_full} = 1;
		}
	}
	else
	{
		_l(2, "Position ".$pos." is not a valid position")
	}
}

# #700101  1:00:00 server id 63  end_log_pos 0    Rotate to mysql-bin.004225  pos: 1011885358
# #091124 11:37:02 server id 63  end_log_pos 0    Start: binlog v 4, server v 5.0.70-enterprise-gpl-log created 091124 11:37:02
# #091124 16:23:39 server id 93  end_log_pos 1011885520   Query   thread_id=1465422711    exec_time=0     error_code=0
sub parse_info
{
	my ($self, $line) = @_;
	$line =~ /^#(\d+)\s+(\d+:\d+:\d+)\s+server\s+id\s+(\d+)\s+end_log_pos\s+(\d+)\s+(\w+)(.*)/;
	my $date = $self->date($1, $2);
	my $server_id = int($3);
	$self->{next_pos} = int($4);
	$self->{type} = lc($5);
	my $more = $6;

	#_d("pos:".$self->{pos}." date:".$self->date." server_id:$server_id next_pos:".$self->{next_pos}." type:".$self->{type}." more:$more");

	# Benchmarked: 'eq' is much faster than regexp :
	#  Rate    regex equality
	#  regex    1088139/s       --     -77%
	#  equality 4716981/s     333%       --

	if ($self->{type} eq 'query' or $self->{type} eq 'xid' or $self->{type} eq 'intvar')
	{
		# how to handle transaction ?
		# more=" = \d+
		$self->{type} = 'query';
	}
	# from 5.5.8
	elsif ($self->{type} eq 'stop')
	{
		$self->{binlogfile} =~ /(.+)\.(\d+)/;
		my ($binlogname, $binlogid) = ($1, int($2));
		$binlogid++;
		$self->{binlogfile} = "$binlogname.$binlogid";
		$self->{pos} = 4;
	}
	# before 5.5.8
	elsif ($self->{type} eq 'rotate')
	{
		# This log appears 2 times: at the start and at the end of the binlog 
		# generated by mysqlbinlog
		# The first one, just before a start, has epoc date
		$more =~ /\s*to\s+(.+?)\s+pos:\s+(\d+)/;
		if ($self->{binlogfile} ne $1)
		{
			$self->{binlogfile} = $1;
			$self->{pos} = $2;
		}
		else
		{
			$self->{type} = 'none';
		}
	}
	elsif ($self->{type} eq 'start')
	{
		$more =~ s/^: //;
		$more =~ /binlog v (\d+),/;
		$self->{version} = int($1);
		$self->{info} = $more;
	}
	else
	{
		_d("[".$self->{type}."] $more");
		_d($line);
	}
}

sub to_s
{
	my ($self) = @_;
	my $delim = $self->{delimiter};
	chomp($delim);
	return "[".$self->{type}."] db:".$self->{db}." date:".strftime('%d/%m/%Y %H:%M:%S', localtime($self->date))." file:".$self->{binlogfile}." pos:".$self->{pos}." next:".$self->{next_pos}." lines:".scalar(@{$self->{sql}});
}

sub query
{
	my ($self) = @_;
	push @{$self->{sql}}, @{$self->{tmpsql}} if (scalar(@{$self->{tmpsql}}) > 0);
	return $self->{sql};
}

sub date
{
	my $self = shift;
	if (@_)
	{
		$self->{date} = join(' ', @_);
		return;
	}
	if ($self->{date} =~ /^\d{6} /)
	{
		my ($year, $month, $day, $hour, $min, $sec) = $self->{date} =~ /^(\d{2})(\d{2})(\d{2}) (\d{1,2}):(\d{1,2}):(\d{1,2})/;
		$year = int($year);
		$year += 100 if ($year < 70); # OK till 2070 ...
		$self->{date} = mktime($sec, $min, $hour, $day, $month-1, $year);
	}
	return $self->{date};
}

sub is_end
{
	my ($self) = @_;
	return $self->{type} eq 'end';
}

sub is_query
{
	my ($self) = @_;
	return $self->{type} eq 'query';
}

sub is_rotate
{
	my ($self) = @_;
	return $self->{type} eq 'rotate' or $self->{type} eq 'stop';
}


1; # }}}

#
# A slave, which launch mysqlbinlog
#
package Slave; # {{{
use warnings FATAL => 'all';
use Carp;
use English qw(-no_match_vars);
use POSIX qw(setsid floor ceil strftime);
use IPC::Open3;
Log->import();
use constant EZDEBUG => $ENV{EZDEBUG} || 0;
use constant PROCESSES => ('IO', 'SQL');
#use constant PROCESSES => ('SQL');

sub new
{
	my $class = shift;
	my ($configfile, $name) = @_;

	my $self = {
		'name'		=> $name,
		'iopid'		=> 0,
		'sqlpid'	=> 0,
		'alive'		=> 1,
		'configfile'=> $configfile,
		'logprefix' => sprintf("%-14s ", $name),
		'stop'		=> 0,
		'error'		=> '',
	};

	bless $self, $class;

	$self->refresh_config;
	$self->{'mgr'} = new SlaveManager($self->{config}, 1);
	foreach my $type (PROCESSES)
	{
		$self->{lc($type)."pid"} = $self->spawn_child($name, $type);
	}
	return $self;
}

sub refresh_config
{
	my ($self) = @_;
	my $config = ConfigIni::parse_ini($self->{configfile});
	if ($config)
	{
		$self->{config} = $config;
		$self->{bigpause} = defined($config->{general}{bigpause}) ? $config->{general}{bigpause} : 10,
	}
}

sub is_alive
{
	my ($self) = @_;
	return 2 if ($self->{alive} == 1); # is starting

	$self->{slave} = $self->{mgr}->get($self->{name});
	$self->{alive} = 0;
	foreach my $type (PROCESSES)
	{
		my $status = $self->{mgr}->get_status($self->{slave}, $type);
		if ($status =~ /^(error|stop)/)
		{
			_d($self->{logprefix}."Slave ".$self->{name}."::$type is not alive");
			$self->{alive}--;
		}
		else
		{
			$self->{alive}++;
		}
	}
	if($self->{alive} > 0 and $self->{alive} < scalar(PROCESSES))
	{
		_l(3, "Partially alive");
	}

	return 0 if ($self->{alive} <= 0);
	return 2 if ($self->{alive} == scalar(PROCESSES));
	return 1; # partial
}

sub stop
{
	my ($self) = @_;
	$self->{stop} = 1;
	foreach my $type (PROCESSES)
	{
		_i('-n', $self->{logprefix}."Stopping ".$self->{name}."::$type : ");

		# Ask child to stop
		# Warning $self->{mgr} is destroyed with the child
		_i('-n', "kill(".$self->{lc($type)."pid"}.")...");
		kill 15, $self->{lc($type)."pid"}; # Child::stop++

		_i('-n', "wait...");
		waitpid($self->{lc($type)."pid"}, 0);
		# done
		_i("done.");
	}
}


sub mysqlbinlog
{
	my ($self, $rl, $delay) = @_;
	my $slave = $self->{slave};
	my $stopdatetime = strftime('%Y-%m-%d %H:%M:%S', localtime(time() - $delay - 60));
	my $mysqlbin = defined($self->{config}{general}{mysqlbin}) ? $self->{config}{general}{mysqlbin} : '/usr/local/mysql/bin';
	my @params = qw/--no-defaults --set-charset UTF8 --read-from-remote-server/;
	push @params, '--user', $slave->{user};
	push @params, '--password', $slave->{password} if ($slave->{password});
	push @params, '--host', $slave->{host} if ($slave->{host});
	push @params, '--port', $slave->{port} if ($slave->{port});
	push @params, '--socket', $slave->{sock} if ($slave->{sock});
	push @params, '--stop-datetime', $stopdatetime;

	$rl->{current_pos} = defined($rl->{current_pos}) ? $rl->{current_pos} : $rl->{start_pos};

	push @params, '--start-position', $rl->{current_pos}, $rl->{binlogfile};
	my @cllog = ($mysqlbin, '/mysqlbinlog ', map { "$_ " } @params);
	_l(3, $self->{logprefix}, grep { $_ !~ /^--password/ } @cllog);

	# TODO: put this open3 in an eval()
	my $mblpid = open3(*BL_IN, *BL_OUT, *BL_ERR, $mysqlbin.'/mysqlbinlog', @params);
	close BL_IN;
	return $mblpid;
}

sub mysqlbinlog_errors
{
	my ($self) = @_;
	#_d($self->{logprefix}."check for mysqlbinlog error");
	my $slave = $self->{slave};
	my @errors = ();
	my $rin = ''; 
	my $rout;
	vec($rin, fileno(BL_ERR), 1) = 1;

	while (select($rout=$rin, undef, undef, 1) > 0 and !eof(BL_ERR))
	{
		my $err = <BL_ERR>;
		if ($err)
		{
			chomp $err;
			if ($err =~ /^Warning:/)
			{
				_l(2, $self->{logprefix}.$err);
			}
			else
			{
				_i($self->{logprefix}."MYSQLBINLOG ".$err);
				push @errors, $err;
				$self->{mgr}->set_status($slave, 'io', 'error: mysqlbinlog');
			}
		}
	}
	
	if (@errors)
	{
		if ($errors[0] =~ /failed on connect:/i
			or (
				$errors[0] =~ /Got error reading packet from server:/ and
				$errors[0] !~ /Could not find first log file name in binary log index file/)
			)
		{
			_i($self->{logprefix}."Will retry in ".$self->{bigpause}."s...");
			sleep $self->{bigpause};
			return 1;
		}
		else
		{
			$self->{mgr}->disable($slave, join("\n", @errors), '');
			$self->{stop} = 1;
			return 2;
		}
	}
	return 0;
}

sub mysqlbinlog_quit
{
	my ($self, $mblpid) = @_;
	close BL_OUT;
	$self->mysqlbinlog_errors();
	close BL_ERR;
	_d($self->{logprefix}."Waiting for mysqlbinlog pid: $mblpid");
	kill 15, $mblpid;
	waitpid($mblpid, 0);
	#if ($? > 0)
	#{
	#	_l(2, $self->{logprefix}."mysqlbinlog exit with code=$?");
	#}
}


sub mysqlclient
{
	my ($self) = @_;
	my $slave = $self->{slave};
	my $mysqlbin = defined($self->{config}{general}{mysqlbin}) ? $self->{config}{general}{mysqlbin} : '/usr/local/mysql/bin';
	my @params = qw/--no-defaults --unbuffered --no-beep --batch --reconnect --wait --skip-column-names/;
	push @params, '--user', $self->{config}{mysql}{user};
	push @params, '--password='.$self->{config}{mysql}{password} if ($self->{config}{mysql}{password});
	push @params, '--host', $self->{config}{mysql}{host} if ($self->{config}{mysql}{host});
	push @params, '--port', $self->{config}{mysql}{port} if ($self->{config}{mysql}{port});
	push @params, '--socket', $self->{config}{mysql}{sock} if ($self->{config}{mysql}{sock});
	my @cllog = ($mysqlbin, '/mysql ', map { "$_ " } @params);
	_l(3, $self->{logprefix}, grep { $_ !~ /^--password/ } @cllog);
	
	my $clpid = open3(*CL_IN, *CL_OUT, *CL_ERR, $mysqlbin.'/mysql', @params);
	CL_IN->autoflush(1);
	return $clpid;
}

sub mysqlclient_errors
{
	my ($self) = @_;
	_d($self->{logprefix}."check for client errors");
	my $slave = $self->{slave};
	my @errors = ();
	my $cin = ''; 
	my $cout;
	vec($cin, fileno(CL_ERR), 1) = 1;
	while (select($cout=$cin, undef, undef, 1) > 0 and !eof(CL_ERR))
	{
		my $err = <CL_ERR>;
		if ($err)
		{
			chomp $err;
			_err($self->{logprefix}."CLIENT ERROR: ".$err);
			push @errors, $err;
			$self->{mgr}->set_status($slave, 'sql', 'error: mysql client');
		}
	}
	# handle mysql client errors
	if(@errors)
	{
		_err($self->{logprefix}."Unable to connect on MySQL, will retry in ".$self->{bigpause}."s...");
		sleep $self->{bigpause};
		return 1;
	}
			
	return 0;
}

sub mysqlclient_quit
{
	my ($self, $clpid) = @_;

	$self->mysqlclient_errors();

	close CL_ERR;
	close CL_IN;
	close CL_OUT;

	_d($self->{logprefix}."Waiting for mysql client pid: $clpid");
	kill 15, $clpid;
	waitpid($clpid, 0);
	if ($? > 0)
	{
		_l(2, $self->{logprefix}."mysql client exit with code=$?");
	}
	# reset SIGPIPE error
	$self->{error} = '';
}

sub IO
{
	my ($self) = @_;
	my $slave = $self->{slave};
	while (!$self->{stop})
	{
		$self->{slave} = $self->{mgr}->get($self->{name});
		$self->{mgr}->set_status($slave, 'io', 'in loop');

		# fetching and parsing mysqlbinlog output
		while (!$self->{error} and !$self->{stop})
		{
			$self->{slave} = $self->{mgr}->get($self->{name});
			$slave = $self->{slave};
			
			# still enable ?
			unless ($slave->{enabled})
			{
				$self->{stop} = 1;
				last;
			}
			
			# On error ? => retry later
			if ($slave->{io_status} =~ /^error/i)
			{
				sleep $self->{bigpause};
				next;
			}

			# Wait if mysql replication is stopped
			my $delay = $self->{mgr}->get_slave_delay();
			if ($delay < 0 or $delay > 120)
			{
				_l(3, $self->{logprefix}." Waiting for master, Seconds_Behind_Master=$delay s") unless ($delay < 0) ;
				sleep $self->{bigpause};
				next;
			}

			# refresh config...
			$self->refresh_config;
			my ($parsed, $added, $excluded) = (0, 0, 0);

			# reset $binlog		
			my $binlog = new Binlog($self->{mgr}->get_last_binlogfile($slave));

			last if ($self->{stop});
			my $mblpid = $self->mysqlbinlog($self->{mgr}->get_last_relaylog($slave), $delay);
			unless($mblpid)
			{
				sleep $self->{bigpause};
				next;
			}

			my $mblerrors = $self->mysqlbinlog_errors();
			next if ($mblerrors == 1); # redo while => retry, paused in mysqlbinlog_errors()
			if ($mblerrors >= 2)
			{
				$self->{error} = "Unable to start mysqlbinlog";
				last; # exit this while
			}

			my $rl = $self->{mgr}->get_last_relaylog($slave);
			unless (open RELAY, ">".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).".tmp")
			{
				_err($self->{logprefix}."unable to open relay log file ".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).": $!");
				sleep $self->{bigpause};
				last;
			}

			# Fetch logs
			_l(2, $self->{logprefix}."RELAYING LOGS to ".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id})." ...");
			$self->{mgr}->set_status($slave, 'io', 'parsing');
			my @logbuffer = ();
			while (!$self->{stop} and !eof(BL_OUT) and my $l = <BL_OUT>) # till end 
			{
				$binlog->parse($l);
				push @logbuffer, $l;
				if ($binlog->is_full)
				{
					$parsed++;
					if ($self->{mgr}->include($slave, $binlog->db) or $binlog->is_end or $binlog->is_rotate)
					{
						# if at the end and not include => keep DELIMITER
						if (($binlog->is_end or $binlog->is_rotate) and !$self->{mgr}->include($slave, $binlog->db))
						{
							# remove everything that is not a SET or DELIMITER or a comment
							@logbuffer = grep { /^(DELIMITER|SET|[\/#])/; } @logbuffer;
						}
						print RELAY "## ".$binlog->to_s.$/;
						print RELAY join('', @logbuffer);
						RELAY->flush();
					}
					else
					{
						print RELAY "## EXCLUDED: ".$binlog->to_s.$/;
						RELAY->flush();
						$excluded++;
					}
					if ($binlog->is_end or $binlog->is_rotate)
					{
						last;
					}

					# to next binlog
					$binlog = new Binlog($binlog->binlogfile, $binlog->next_pos, $binlog->db, $binlog->delimiter_def);
					@logbuffer = ();
				}
			}
			close RELAY;
			$added = $parsed - $excluded;
			_l(3, $self->{logprefix}."$parsed parsed, $excluded excluded => $added new");
			$self->mysqlbinlog_quit($mblpid);

			if (!$self->{error} and ($binlog->is_end or $binlog->is_rotate))
			{
				if ($binlog->is_rotate or ($parsed > 2 and $added > 2))
				{
					my $gzipped = "";
					# Try to gzip relay log file
					if (system("/bin/gzip -1 '".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).".tmp"."'") == 0)
					{
						$gzipped = ".gz";
					}
					else
					{
						_l(2, $self->{logprefix}."unable to gzip ".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).".tmp");
					}

					unless(rename($self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).".tmp".$gzipped, $self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).$gzipped))
					{
						_l(2, $self->{logprefix}."unable to rename ".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).".tmp".$gzipped." to ".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).$gzipped." : $!");
					}

					# Next position is next_pos if not at the end of the binary log
					my $nextpos = $binlog->{next_pos};
					$nextpos = $binlog->{pos} if ($binlog->{pos} == 4);
					if ($binlog->{pos} == 4)
					{
						_d($binlog->to_s);
					}
					_l(3, $self->{logprefix}."END, next will be ".$binlog->{binlogfile}.":".$nextpos);
					$self->{mgr}->add_relaylog($slave, $binlog->{binlogfile}, $nextpos, $binlog->{date});
				}
				else
				{
					_l(3, $self->{logprefix}."END, no new logs, sleeping more");
					unlink($self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).".tmp");
					sleep $self->{bigpause};
				}
			}
			else
			{
				_err("Relay log not fully parsed, removing temporary file");
				unlink($self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).".tmp");
			}
			_d($self->{logprefix}."sleep $self->{bigpause}");
			sleep $self->{bigpause} unless ($self->{stop});
		}
		close RELAY; # if while exited with last;
		_d($self->{logprefix}."End read mysqlbinlog output loop");

		# error management
		if (!$self->{stop} and $self->{error})
		{
			_l(2, $self->{logprefix}.$self->{error}.", sleeping ".$self->{bigpause}."s");
			$self->{mgr}->set_status($slave, 'io', 'sleeping');
			sleep $self->{bigpause};
		}
	}
	_l(3, $self->{logprefix}."exiting.");
	$self->{mgr}->set_status($slave, 'io', 'stopped');
	return 0; # exit code
}


sub SQL
{
	my ($self) = @_;
	my $slave = $self->{slave};
	while (!$self->{stop})
	{
		$self->{mgr}->set_status($slave, 'sql', 'in loop');

		# Launch mysql client
		my $clpid = $self->mysqlclient();
		
		# check for errors
		if ($self->mysqlclient_errors())
		{
			_err($self->{logprefix}.$self->mysqlclient_errors());
			next;
		}
		
		# fetching and parsing mysqlbinlog output
		my $binlog;
		while (!$self->{error} and !$self->{stop})
		{
			$self->{dbdefined} = 0; # sql definitions (use, delimiter, ...)
			# still enable ?
			$self->{slave} = $self->{mgr}->get($self->{name});
			$slave = $self->{slave};
			unless ($slave->{enabled})
			{
				$self->{stop} = 1;
				_l(3, $self->{logprefix}."this slave is disabled.");
				last;
			}
			
			# On error ? => retry later
			if ($slave->{sql_status} =~ /^error/i)
			{
				_l(3, $self->{logprefix}."this slave is on error.");
				sleep $self->{bigpause};
				next;
			}

			# refresh config...
			$self->refresh_config;
			# restart mysqlbinlog if closed (when end is reached, or rotate)
			$self->{slave} = $self->{mgr}->get($self->{name});

			my $binlog = new Binlog($self->{mgr}->get_current_binlogfile($slave));

			last if ($self->{stop});
			
			my $rl = $self->{mgr}->get_current_relaylog($slave);
			unless(defined($rl))
			{
				_i($self->{logprefix}."relay log file undefined yet");
				$self->{mgr}->set_status($slave, 'sql', 'no relay log');
				sleep $self->{bigpause};
				next;
			}
			if (-e $self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).".gz")
			{
				_l(4, $self->{logprefix}."Decompressing relaylog file ...");
				if (system("/bin/gzip -d '".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).".gz'") > 0)
				{
					_err($self->{logprefix}."unable to gunzip ".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).".gz: $!");
					sleep $self->{bigpause};
					next;
				}
			}
			unless(-e $self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}))
			{
				_l(3, $self->{logprefix}."Waiting for ".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}));
				sleep $self->{bigpause};
				next;
			}
			unless (open RELAY_IN, $self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}))
			{
				_err($self->{logprefix}."unable to open ".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id}).": $!");
				sleep $self->{bigpause};
				next;
			}

			# Parse and handle logs
			my ($handled, $skipped) = (0, 0);
			_l(2, $self->{logprefix}."PARSING RELAY LOG ".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id})." ...");
			$self->{mgr}->set_status($slave, 'sql', 'parsing');
			my $start = time();
			while (!$self->{stop} and !$self->{error} and !eof(RELAY_IN) and my $l = <RELAY_IN>) # till end 
			{
				$binlog->parse($l);
				if ($binlog->is_full)
				{
					if ($binlog->version > 0 and $binlog->version < 4)
					{
						$self->{error} = "This version of binary log is not supported: ".$binlog->version;
						last;
					}
					# Start to handle after current_pos
					# but skip only "query" type
					if (defined($rl->{current_pos}) and $binlog->pos < $rl->{current_pos} and $binlog->is_query)
					{
						$skipped++;
						#_d("Skipped: ".$binlog->pos." < ".$rl->{current_pos}." : ".$binlog->to_s);
					}
					# --skip [--offset=i]
					elsif (defined($rl->{skip}) and $rl->{skip} =~ /\d+/ and $rl->{skip} > 0 and $binlog->is_query)
					{
						$rl->{skip}--;
						$self->{mgr}->skip($slave, $rl->{skip});
						_l(3, "skipped (offset=".$rl->{skip}.")");
					}
					elsif ($self->handle_log($slave, $binlog, $rl))
					{
						$handled++;
					}
					else
					{
						$self->{error} = "Problem to handle ".$binlog->to_s;
						last;
					}

					# to next binlog
					$binlog = new Binlog($binlog->binlogfile, $binlog->next_pos, $binlog->db, $binlog->delimiter_def);
				}
				if ((time() - $start) > 3600/2)
				{
					$self->{error} = "Timeout (".(time()-$start).") to handle relaylog ".$self->{mgr}->get_relaylog_file($slave->{name}, $rl->{id});
				}
			}
			close RELAY_IN;
			_l(2, $self->{logprefix}."$handled handled".($skipped > 0 ? ", $skipped skipped" : ''));
			#$self->{error} = "No new logs available" if ($handled <= 2);
			$self->handle_error("end handle_logs");
			if ($self->{error} =~ /Duplicate entry/ and $self->{config}->{general}{skip_duplicates} =~ /yes/i)
			{
				_err($self->{logprefix}.$self->{error});
			}
			elsif ($self->{error})
			{
				_err($self->{logprefix}.$self->{error});
				_d($self->{logprefix}."sleep $self->{bigpause}");
				sleep $self->{bigpause};
			}
			else
			{
				unless($self->{mgr}->next_relaylog($slave))
				{
					_l(3, $self->{logprefix}."No new relay logs available, waiting $self->{bigpause}s");
					sleep $self->{bigpause};
				}
				$self->{mgr}->remove_relaylog($self->{logprefix}, $slave, $rl);
			}
		}

		$self->mysqlclient_quit($clpid);
		
		# error management
		if (!$self->{stop} and $self->{error})
		{
			_l(2, $self->{logprefix}.$self->{error}.", sleeping ".$self->{bigpause}."s");
			$self->{mgr}->set_status($slave, 'sql', 'sleeping');
			sleep $self->{bigpause};
		}
	}
	_l(3, $self->{logprefix}."exiting.");
	$self->{mgr}->set_status($slave, 'sql', 'stopped');
	return 0; # exit code
}


sub spawn_child # {{{
{
	my ($self, $name, $type) = @_;

	if(my $pid = fork())
	{	# Parent
		return $pid;
	}
	elsif(defined $pid)
	{	# Child
		# child process name
		my $progname = $0;
		$0 = $progname."::$name"."::$type";

		# we need to reinstance the slave obj, to have a proper DBH:
		$self->{slave} = $self->{mgr}->get($self->{name});
		my $slave = $self->{slave};


		local $SIG{INT} = $SIG{TERM} = sub { _d($self->{logprefix}."got SIG".(shift @_)); $self->{stop}=1; } ;
		local $SIG{PIPE} = sub { $self->handle_error('SIGPIPE'); } ;
		local $SIG{HUP} = 'DEFAULT';

		local (*CL_IN, *CL_OUT, *CL_ERR);
		local (*BL_IN, *BL_OUT, *BL_ERR);

		$self->{logprefix} = sprintf("%-14s ", $name."::$type");
		exit $self->$type();
	}
	else
	{
		_err($self->{logprefix}."fork failed: $!");
		die "fork failed: $!";
	}
	_d($self->{logprefix}."SHOULD NOT BE HERE => BUG ?");
} # }}}

sub handle_log
{
	my ($self, $slave, $log, $rl) = @_;
	my $db = $self->{config}->{management}{database};
	$self->{currentlog} = $log; # for handle_error in case of SIGPIPE

	# Some sanity checks
	unless($db)
	{
		_err($self->{logprefix}."MSR database not set.");
		return 0;
	}

	# set pos and next_pos BEFORE query
	my $uqr = "UPDATE /* BEFORE */ `$db`.`relaylogs` SET current_pos=".$log->pos." WHERE id=".$rl->{id}.$log->delimiter;
	unless(print CL_IN $uqr)
	{
		return $self->handle_error($log);
	}

	# First query: put SETUP queries like DELIMITER and USE
	if ($self->{dbdefined} == 0 and $log->db)
	{
		unless(print CL_IN "use ".$log->db.$log->delimiter)
		{
			return $self->handle_error($log);
		}
		$self->{dbdefined}++;
	}
	
	foreach my $uq (@{$log->query})
	{
		unless(print CL_IN $uq)
		{
			return $self->handle_error($log);
		}
	}

	#
	# SUCCESS => update position
	#
	$uqr = "UPDATE /* AFTER */ `$db`.`relaylogs` SET current_pos=".$log->next_pos." WHERE id=".$rl->{id}.$log->delimiter;
	unless(print CL_IN $uqr)
	{
		# TODO: use $self->{mgr} to force the update of the position
		return $self->handle_error($log);
	}
}

sub handle_error
{
	my ($self, $error_or_log) = @_;
	my $rin = ''; 
	my $rout;

	my $error = $error_or_log;
	my $log;
	if ($error_or_log->isa('Binlog'))
	{
		$log = $error_or_log;
	}
	elsif (defined($self->{currentlog}) and $self->{currentlog}->isa('Binlog'))
	{
		$log = $self->{currentlog};
	}
	$self->{currentlog} = undef;

	return 1 unless(defined(fileno(CL_ERR)));
	vec($rin, fileno(CL_ERR), 1) = 1;
	_err($self->{logprefix}."handle_error ".$error) unless (defined($log));
	if (select($rout=$rin, undef, undef, 1) > 0)
	{
		my $slave = $self->{mgr}->get($self->{name});
		while (<CL_ERR>)
		{
			chomp;
			_err($self->{logprefix}.$_);
			$self->{error} = $_;
			my $disableme = 0;
			my $stopme = 0;
			# 1062 = Duplicate entry
			# 2006 = Has gone away
			if (/^ERROR (2006|2013)/)
			{
				return 1;
			}
			elsif (/^ERROR (1062)/)
			{
				if ($self->{config}->{general}{skip_duplicates} =~ /yes/i)
				{
					$self->{mgr}->skip($slave, 1);
					return 2;
				}
				else
				{
					$stopme = 0;
					$disableme = 1;
				}
			}
			# All errors except 1317
			unless (/^ERROR (1317)/)
			{
				$stopme = 1;
				$disableme = 1;
			}
			if ($disableme)
			{
				$self->{mgr}->disable($slave, '', $self->{error}.$/.(defined($log) ? $log->to_s : $error));
			}
			$self->{stop} = 1 if ($stopme);
			return 0;
		}
	}
	# no errors detected, however did we have a SIGPIPE ?
	if ($error eq 'SIGPIPE')
	{
		$self->{error} = 'SIGPIPE' unless ($self->{error});
		return 0 ;
	}
	return 1;
}

1; # }}}

#
# Slaves manager: 
# manage slaves status, position, ...
#
package SlaveManager; # {{{

use strict;
use warnings FATAL => 'all';
use English qw(-no_match_vars);
use DBI; # only for slave configuration, not for binlog injection.
Log->import();

my %tables = ( # {{{
	'masters' => "CREATE TABLE IF NOT EXISTS masters (
	`id` smallint unsigned NOT NULL AUTO_INCREMENT,
	`name` varchar(60) DEFAULT NULL,
	`host` varchar(60) DEFAULT NULL,
	`user` varchar(16) DEFAULT NULL,
	`password` varchar(41) DEFAULT NULL,
	`port` smallint unsigned DEFAULT 3306,
	`sock` varchar(60) DEFAULT NULL,
	`enabled` tinyint unsigned DEFAULT 1,
	`relay_id` int unsigned DEFAULT 0,
	`io_status` smallint unsigned DEFAULT 0,
	`io_error` varchar(512) DEFAULT NULL,
	`sql_status` smallint unsigned DEFAULT 0,
	`sql_error` varchar(512) DEFAULT NULL,
	PRIMARY KEY (`id`, `name`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8",
	'relaylogs' => "CREATE TABLE IF NOT EXISTS relaylogs (
	`id` int unsigned NOT NULL AUTO_INCREMENT,
	`master_id` smallint unsigned NOT NULL,
	`binlogfile` varchar(255) DEFAULT NULL,
	`start_pos` int unsigned DEFAULT NULL,
	`current_pos` int unsigned DEFAULT NULL,
	`skip` smallint unsigned DEFAULT NULL,
	`end_pos` int unsigned DEFAULT NULL,
	`date` TIMESTAMP DEFAULT NULL,
	PRIMARY KEY (`id`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8",
	'master_greylist' => "CREATE TABLE IF NOT EXISTS master_greylist (
	`id` int unsigned NOT NULL AUTO_INCREMENT,
	`master_id` smallint unsigned NOT NULL,
	`db` varchar(60) DEFAULT NULL,
	`include_or_exclude` tinyint unsigned NOT NULL,
	PRIMARY KEY (`id`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8"
); # }}}
my @STATUS = (
				'stopped',
				'starting',
				'in loop',
				'error: mysql client',
				'error: mysqlbinlog',
				'parsing',
				'handling',
				'waiting',
				'sleeping',
				'disabled',
				'no relay log'
);


sub new
{
	my ($class, $config, $initonly) = @_;

	my $self = $config->{management};
	$self->{config} = $config->{general};
	$self->{dbh} = undef;
	$self->{setup} = defined($self->{setup}) ? $self->{setup} : 0;
	bless $self, $class;
	$initonly = 0 unless(defined($initonly));

	$self->init() unless($initonly);
	return $self;
}

sub init
{
	my ($self) = @_;
	_d("SlaveManager is initializing");

	for (my $i=0; $i<10; $i++)
	{
		last if $self->is_connected;
		_l(2, "Unable to connect #".($i+1));
		sleep 1;
	}
	die "Unable to connect to database." if (!$self->{dbh});

	$self->fetch unless ($self->{setup});
}

sub DESTROY
{
	my ($self) = @_;
	$self->disconnect;
}

sub connect
{
	my ($self) = @_;
	if (!$self->{dbh} or !$self->{dbh}->ping)
	{
		_d("$$ Connecting to database");
		my $db = ($self->{setup} == 1) ? "mysql" : $self->{database};
		
		my $dbih = "DBI:mysql:database=".$db;
		if ($self->{sock})
		{
			$dbih .= ";mysql_socket=".$self->{sock};
		}
		else
		{
			$dbih .= ";host=".$self->{host};
			$dbih .= ";port=".$self->{port} if ($self->{port});
		}
		$dbih .= ";mysql_auto_reconnect=1;mysql_enable_utf8=1";
		my $h = DBI->connect(
				$dbih,
				$self->{user},
				$self->{password},
				{
					'RaiseError' => 0,
					'PrintError' => 0,
					'HandleError' => sub { _err($_[0]); }, # log errors to logger
				},
			);
		if ($h)
		{
			$h->do("SET NAMES utf8");
			$self->{dbh} = $h;
		}
	}
}

sub disconnect
{
	my ($self) = @_;
	if ($self->{dbh})
	{
		_d('SlaveManager is disconnecting from DB');
		$self->{dbh}->disconnect;
		$self->{dbh} = undef;
	}
}

sub list_slaves
{
	my ($self, $enabled) = @_;
	if ($enabled)
	{
		$self->fetch();
		my @keys;
		for my $key (keys %{$self->{slaves}})
		{
			push @keys, $key if ($self->{slaves}->{$key}{enabled});
		}
		return @keys;
	}
	return keys %{$self->{slaves}};
}

sub slaves
{
	my ($self, $enabled) = @_;
	return $self->{slaves};
}

sub get
{
	my ($self, $name) = @_;
	$self->fetch();
	return $self->{slaves}->{$name};
}

sub setup_db
{
	my ($self) = @_;
	my $db = $self->{dbh};
	my $error = 0;
	_i("Checking if database '$self->{database}' exists");
	my $found = 0;
	for my $dbname (@{$db->selectall_arrayref("SHOW DATABASES")})
	{
		if ($dbname->[0] eq $self->{database})
		{
			$found = 1;
			last;
		}
	}
	unless ($found)
	{
		_i("Creating database '$self->{database}'");
		unless($db->do("CREATE DATABASE \`$self->{database}\`"))
		{
			_err("Unable to create database '$self->{database}'");
			$error = 1;
		}
	}

	_l(2, "Reconnecting");
	$self->disconnect;
	$self->{setup} = 2;
	$self->connect;
	$db = $self->{dbh};

	while (my ($name, $create) = each %tables)
	{
		_i("Checking table $name");
		unless($db->do($create))
		{
			_err($DBI::errstr);
			$error = 2;
		}
	}
	_i("Setup done.");
	return $error;
}

sub is_connected
{
	my ($self, $name) = @_;
	$self->connect;
	return $self->{dbh} ? 1 : 0;
}

sub _hashref_to_slave
{
	my $slave = shift;
	for my $key (qw(port next_pos pos id enabled io_status sql_status offset))
	{
		$slave->{$key} = defined($slave->{$key}) ? int($slave->{$key}) : 0;
	}
	return $slave;
}

sub print_slave
{
	my ($self, $name) = @_;
	unless ($self->exists($name))
	{
		_err("Slave ".$name." does not exists.");
		return 1; # exit code
	}
	my $slave = $self->{slaves}->{$name};
	my $relaylogs = $self->get_relay_logs($slave);
	my $rl = $relaylogs->{$slave->{relay_id}};
	my $inf = "[".$slave->{id}."]$name: ";
	$inf .= "sock:".$slave->{sock} if (defined($slave->{sock}));
	$inf .= $slave->{host}.":".$slave->{port} if (defined($slave->{host}));
	$inf .= " relay log ".$rl->{id}.": ".$rl->{binlogfile}.":".$rl->{start_pos}.(defined($rl->{current_pos}) ? " at ".$rl->{current_pos} : '').(defined($rl->{end_pos}) ? " to ".$rl->{end_pos} : '') if ($rl);
	_i($inf);
}

sub fetch
{
	my ($self, $name) = @_;
	unless ($self->is_connected)
	{
		_l(2, "Not connected to DB");
		return 0;
	}
	my %slaves = %{$self->{dbh}->selectall_hashref("SELECT * FROM masters", [ qw(name) ])};
	unless(%slaves)
	{
		_l(2, "Unable to SELECT masters");
		return 0;
	}
	foreach my $slave (keys %slaves)
	{
		$slaves{$slave} = _hashref_to_slave($slaves{$slave});
	}
	if (%slaves)
	{
		$self->{slaves} = \%slaves;
		return 1;
	}
	else
	{
		_d("no slaves found");
	}
	return 0;
}

sub exists
{
	my ($self, $name) = @_;
	$self->fetch();
	$name = $name->{name} if (ref $name eq 'HASH');
	foreach my $slave (keys %{$self->{slaves}})
	{
		return 1 if ($name eq $slave)
	}
	return 0;
}

sub add
{
	my ($self, $slave) = @_;
	if ($self->exists($slave))
	{
		_i("Slave ".$slave->{name}." already exists.");
		return 1; # exit code
	}
	$slave = _hashref_to_slave($slave);
	# a slave must have a name, host|sock, user, binlogfile (pos could be 0)
	unless ($slave->{binlogfile} 
		and ($slave->{host} or $slave->{sock}) 
		and $slave->{user}
		and $slave->{name})
	{
		_i("To add a slave you need to specify at least:");
		_i("name, host or socket, user, binlogfile");
		for my $d (qw(name host sock user binlogfile))
		{
			_i("Missing: $d") unless (defined($slave->{$d}));
		}
		return 2;
	}

	$slave->{enabled} = 1 if ($slave->{enable});
	$slave->{enabled} = 0 if ($slave->{disable});
	return 1 unless ($self->is_connected);
	unless ($self->{dbh}->do(q{INSERT INTO masters SET id = NULL, name = ?}, undef, $slave->{name}))
	{
		_err("Unable to add a master row : ".$self->{dbh}->errstr);
		return 2;
	}
	$slave->{id} = $self->{dbh}->last_insert_id(undef, undef, undef, undef);
	return $self->change($slave);
}

sub remove
{
	my ($self, $slave) = @_;
	unless ($self->exists($slave))
	{
		_err("Slave $slave does not exists.");
		return 0; # exit code
	}
	$slave = _hashref_to_slave($slave);
	$self->fetch();
	$slave = $self->{slaves}->{$slave->{name}};
	unless ($self->{dbh}->do("DELETE FROM relaylogs WHERE master_id = ?", undef, $slave->{id}))
	{
		_err("Unable to remove relay logs for this slave: ".$self->{dbh}->errstr);
	}
	unless ($self->{dbh}->do("DELETE FROM masters WHERE id = ?", undef, $slave->{id}))
	{
		_err("Unable to remove this slave: ".$self->{dbh}->errstr);
		return 2;
	}
	
	$self->fetch();
	_i("Slave ".$slave->{name}." removed.");
	return 0;
}

sub change
{
	my ($self, $slave) = @_;
	unless ($self->exists($slave))
	{
		_err("Slave ".$slave->{name}." does not exists.");
		return 1; # exit code
	}
	$slave = _hashref_to_slave($slave);
	# merge current and new slave infos
	for my $key (keys %{$slave})
	{
		$self->{slaves}->{$slave->{name}}{$key} = $slave->{$key} if ($slave->{$key});
	}

	# Check IP
	use Socket;
	my $h;
	my $packed_ip = gethostbyname($self->{slaves}->{$slave->{name}}{host});
	$h = inet_ntoa($packed_ip) if (defined($packed_ip));
	unless(defined($h))
	{
		_err("Host ".$self->{slaves}->{$slave->{name}}{host}." not found.");
		return 3;
	}
	_d(inet_ntoa($packed_ip));

	# Change main informations
	my $query = "UPDATE masters SET ";
	my @bindvalues;
	foreach my $key (qw{host user password port sock enabled})
	{
		$query .= "$key = ? ,";
		push @bindvalues, $self->{slaves}->{$slave->{name}}{$key};
	}
	$query = substr($query, 0, -1);
	$query .= " WHERE id=?";
	push @bindvalues, $self->{slaves}->{$slave->{name}}{id};

	unless ($self->{dbh}->do($query, undef, @bindvalues))
	{
		_i("Unable to change master row : ".$self->{dbh}->errstr);
		return 2;
	}
	$self->fetch();

	# Change binlog file and position
	if (defined($slave->{binlogfile}))
	{
		if ($self->{slaves}->{$slave->{name}}{enabled} and $self->{slaves}->{$slave->{name}}{io_status} > 0)
		{
			_err("Could not change binlog file and position as this slave is enabled and running");
		}
		else
		{
			_l(2, "Updating position to ".$slave->{binlogfile}.":".$slave->{pos});

			_l(3, "Removing relay logs");
			my $relaylogs = $self->get_relay_logs($slave);
			while (my ($rlid, $rl) = each(%$relaylogs))
			{
				_d("[".$rl->{id}."] ".$rl->{binlogfile}.":".$rl->{start_pos});
				$self->remove_relaylog('', $self->{slaves}->{$slave->{name}}, $rl);
			}
			my $rl = $self->add_relaylog($slave, $slave->{binlogfile}, $slave->{pos});
			return 2 unless $self->set_relaylog($slave, $rl);
		}
	}
	
	$self->print_slave($slave->{name});
	return 0;
}

sub get_relaylog_file
{
	my ($self, $name, $id) = @_;
	my $logsdir = defined($self->{config}{logsdir}) ? $self->{config}{logsdir} : '/tmp/msr';
	if (!-d $logsdir)
	{
		_l(2, "Creating relay logs directory: $logsdir");
		unless(mkdir($logsdir, 0700))
		{
			_err("unable to mkdir: $!");
		}
	}
	if (!-d "$logsdir/$name")
	{
		_l(2, "Creating relay logs directory: $logsdir/$name");
		unless(mkdir("$logsdir/$name", 0700))
		{
			_err("unable to mkdir: $!");
		}
	}
	return $logsdir."/".$name."/relaylog-".$id.".log";
}

sub skip
{
	my ($self, $slave, $offset) = @_;
	unless ($self->exists($slave))
	{
		_err("Slave ".$slave->{name}." does not exists.");
		return 1; # exit code
	}
	$slave = _hashref_to_slave($slave);
	$self->fetch();
	$offset = defined($offset) ? int($offset) : 1;
	$offset = (defined($slave->{offset}) and $slave->{offset} > 0) ? int($slave->{offset}) : $offset;
	$offset = 'NULL' if ($offset <= 0);
	my $rl = $self->get_current_relaylog($slave);
	$slave = $self->{slaves}->{$slave->{name}};
	$self->is_connected();
	my $query = "UPDATE relaylogs SET skip=$offset WHERE master_id=? AND id=?";
	my @bindvalues = ($slave->{id}, $rl->{id});
	unless ($self->{dbh}->do($query, undef, @bindvalues))
	{
		_err("Unable to update a row in relaylogs table : ".$self->{dbh}->errstr);
	}
	_d("Configured to skip $offset entries");
	return 0;
}

sub enable
{
	my ($self, $slave, $enabled, $io_error, $sql_error) = @_;
	$enabled = defined($enabled) ? $enabled : 1;

	# If disabling for error, do not really disable :
	if (!$enabled and (defined($io_error) or defined($sql_error)))
	{
		$enabled = 1;
	}

	$io_error = defined($io_error) ? $io_error : '';
	$sql_error = defined($sql_error) ? $sql_error : '';
	unless ($self->exists($slave))
	{
		_err("Slave ".$slave->{name}." does not exists.");
		return 1; # exit code
	}
	_d(($enabled ? 'enabling' : 'disabling')." slave ".$slave->{name});
	$slave = _hashref_to_slave($slave);
	$self->fetch();
	$slave = $self->{slaves}->{$slave->{name}};

	unless ($self->{dbh}->do("UPDATE masters SET enabled = ?, io_error = ?, sql_error=? WHERE id = ?", undef, ($enabled, $io_error, $sql_error, $slave->{id})))
	{
		_err("Unable to ".($enabled ? 'enable' : 'disable')." slave[".$slave->{id}."]: ".$self->{dbh}->errstr);
		return 2;
	}
	
	_i("Slave ".$slave->{name}." ".($enabled ? 'ENABLED' : 'DISABLED'));
	return 0;
}

sub disable
{
	my ($self, $slave, $io_error, $sql_error) = @_;
	my $emailbody;
	if ($io_error)
	{
		$emailbody = "Slave ".$slave->{name}." got an IO error: $io_error";
		_err($emailbody);
		$self->set_status($slave, 'io', 'error: mysqlbinlog');
	}
	elsif ($sql_error)
	{
		$emailbody = "Slave ".$slave->{name}." got an SQL error: $sql_error";
		_err($emailbody);
		$self->set_status($slave, 'sql', 'error: mysql client');
	}
	else
	{
		_err("Slave ".$slave->{name}." is disabled.");
		$self->set_status($slave, 'io' , 'disabled');
		$self->set_status($slave, 'sql', 'disabled');
	}
	eval
	{
		if (open(MAIL, "| mail -s '[ALERT] $0' '".$self->{config}{email}."'"))
		{
			print MAIL $emailbody.$/;
			close MAIL;
		}
	};
	if ($@)
	{
		_err("Unable to send alert mail: $@");
	}
	return $self->enable($slave, 0, $io_error, $sql_error);
}

sub get_status
{
	my ($self, $slave, $type) = @_;
	unless ($self->exists($slave))
	{
		_err("Slave ".$slave->{name}." does not exists.");
		return 1; # exit code
	}
	$slave = _hashref_to_slave($slave);
	$self->fetch();
	return $STATUS[$slave->{lc($type)."_status"}];
}

sub set_status
{
	my ($self, $slave, $type, $status) = @_;
	unless ($self->exists($slave))
	{
		_err("Slave ".$slave->{name}." does not exists.");
		return 1; # exit code
	}
	return 0 unless($type =~ /^io|sql$/i);
	$slave = _hashref_to_slave($slave);
	my $i = 0;
	for($i=0; $i<scalar(@STATUS); $i++)
	{
		if ($STATUS[$i] =~ /$status/i)
		{
			last;
		}
	}
	if (exists($STATUS[$i]))
	{
		$self->is_connected();
		my $query = "UPDATE masters SET ".lc($type)."_status=$i WHERE id=".$self->{slaves}->{$slave->{name}}{id};
		unless ($self->{dbh}->do($query))
		{
			_err("Unable to set ".lc($type)."_status=$status for ".$slave->{name}." : ".$self->{dbh}->errstr);
			return 2;
		}
	}
}

# does not do a $self->exists as it would do a fetch which do a query
# this function doesn't have to do any query, or at least cache it
sub include
{
	my ($self, $slave, $db) = @_;
	return 1 if ($db eq '');
	return 0 unless(exists($self->{slaves}->{$slave->{name}}));
	$slave = $self->{slaves}->{$slave->{name}};

	# query and cache
	unless(exists($self->{slaves}->{$slave->{name}}{gl}))
	{
		$self->is_connected();
		#_d($slave->{name}.": fetch greylist");
		my $gl = $self->{dbh}->selectall_hashref("SELECT db, include_or_exclude FROM master_greylist WHERE master_id=".$slave->{id}, [ qw(db) ]);
		my %greylist;
		foreach my $g (keys %$gl)
		{
			$greylist{$g} = $gl->{$g}{include_or_exclude};
		}
		$self->{slaves}->{$slave->{name}}{gl} = \%greylist;
	}

	# if present in greylist AND include_or_exclude=1
	if(exists($self->{slaves}->{$slave->{name}}{gl}->{$db}))
	{
		return 1 if($self->{slaves}->{$slave->{name}}{gl}->{$db} > 0);
		return 0;
	}

	# not present and greylist has include: exclude
	my $has_include = 0;
	foreach my $d (keys %{$self->{slaves}->{$slave->{name}}{gl}})
	{
		return 0 if ($self->{slaves}->{$slave->{name}}{gl}->{$d} > 0);
	}
	# not present and greylist has exclusion or not configure: include
	return 1;
}

sub get_relay_logs
{
	my ($self, $slave) = @_;
	return 0 unless(exists($self->{slaves}->{$slave->{name}}));
	$self->is_connected();
	$slave = $self->{slaves}->{$slave->{name}};
	return $self->{dbh}->selectall_hashref("SELECT * FROM relaylogs WHERE master_id=".$slave->{id}." ORDER BY id", [ qw(id) ]);
}

sub get_slave_delay
{
	my ($self) = @_;
	unless ($self->is_connected())
	{
		_l(2, "Main MySQL SQL Slave is unavailable !");
		return -1;
	}
	my $sss = $self->{dbh}->selectrow_hashref("SHOW SLAVE STATUS");

	# slave not running
	if ($sss->{Slave_SQL_Running} !~ /yes/i)
	{
		_l(2, "Main MySQL SQL Slave is stopped...");
		return -2;
	}
	
	# seconds behind master
	my $s = $sss->{Seconds_Behind_Master};
	if ($s eq 'NULL')
	{
		_l(2, "Main MySQL SQL Slave is stopped...");
		return -3;
	}
	return int($s);
}

sub get_current_binlogfile
{
	my ($self, $slave) = @_;
	my $rl = $self->get_current_relaylog($slave);
	return defined($rl) ? $rl->{binlogfile} : '';
}

sub get_last_binlogfile
{
	my ($self, $slave) = @_;
	my $rl = $self->get_last_relaylog($slave);
	return defined($rl) ? $rl->{binlogfile} : '';
}

sub get_current_relaylog
{
	my ($self, $slave) = @_;
	return undef unless(exists($self->{slaves}->{$slave->{name}}));
	$slave = $self->{slaves}->{$slave->{name}};
	my $relaylogs = $self->get_relay_logs($slave);
	unless(defined($relaylogs->{$slave->{relay_id}}))
	{
		return undef;
	}
	return $relaylogs->{$slave->{relay_id}};
}

sub get_last_relaylog
{
	my ($self, $slave) = @_;
	return undef unless(exists($self->{slaves}->{$slave->{name}}));
	$slave = $self->{slaves}->{$slave->{name}};
	my $relaylogs = $self->get_relay_logs($slave);
	my $lrl = $relaylogs->{(sort { $a <=> $b } keys %$relaylogs)[-1]};
	return $lrl;
}

sub add_relaylog
{
	my ($self, $slave, $binlogfile, $pos, $date) = @_;
	$date = 'NULL' unless(defined($date));
	$self->is_connected();
	my $query = "INSERT INTO relaylogs SET master_id=?, binlogfile=?, start_pos=?, date=FROM_UNIXTIME(?)";
	my @bindvalues = ($self->{slaves}->{$slave->{name}}{id}, $binlogfile, $pos, $date);

	unless ($self->{dbh}->do($query, undef, @bindvalues))
	{
		_err("Unable to insert a row in relaylogs table : ".$self->{dbh}->errstr);
		return 0;
	}

	my $newrl = $self->{dbh}->last_insert_id(undef, undef, undef, undef);
}

sub set_relaylog
{
	my ($self, $slave, $rlid) = @_;
	unless($rlid and $rlid =~ /^\d+$/)
	{
		_err("Invalid relay log ID: $rlid");
		return 0;
	}
	$self->is_connected();
	my $query = "UPDATE masters SET relay_id=? WHERE id=?";
	my @bindvalues = ($rlid, $self->{slaves}->{$slave->{name}}{id});
	unless ($self->{dbh}->do($query, undef, @bindvalues))
	{
		_err("Unable to change master row : ".$self->{dbh}->errstr);
		return 0;
	}
	return 1;
}

sub next_relaylog
{
	my ($self, $slave) = @_;
	my $relaylogs = $self->get_relay_logs($slave);
	my $crl = $self->get_current_relaylog($slave);
	my $next = 0;
	return 0 unless(defined($crl));
	foreach my $rl (sort { $a <=> $b } keys %$relaylogs)
	{
		if ($next)
		{
			$next = $rl;
			last;
		}
		if ($crl->{id} == $relaylogs->{$rl}->{id})
		{
			$next = 1;
		}
	}
	if ($next == 1)
	{
		return 0;
	}
	#_d("Next relay log to handle: $next");
	return $self->set_relaylog($slave, $next) if ($next);
	return 0;
}

sub remove_relaylog
{
	my ($self, $lp, $slave, $rl) = @_;
	my $rlfile = $self->get_relaylog_file($slave->{name}, $rl->{id});
	if (-e $rlfile)
	{
		#if (open(R, ">>to_remove.sh"))
		if (unlink($rlfile))
		{
			#system("gzip -9 $rlfile");
			#print R "rm -v $rlfile.gz$/";
			_d("$lp$rlfile removed");
			#close R;
		}
		else
		{
			_err($lp."Unable to remove $rlfile : $!");
		}
	}
	$self->is_connected();
	my $query = "DELETE FROM relaylogs WHERE master_id=? AND id=?";
	my @bindvalues = ($slave->{id}, $rl->{id});
	unless ($self->{dbh}->do($query, undef, @bindvalues))
	{
		_err($lp."Unable to remove a row in relaylogs table : ".$self->{dbh}->errstr);
	}
}

1; # }}}



# ###########################################################################
# This is a combination of modules and programs in one -- a runnable module.
# http://www.perl.com/pub/a/2006/07/13/lightning-articles.html?page=last
# Or, look it up in the Camel book on pages 642 and 643 in the 3rd edition.
#
# Check at the end of this package for the call to main() which actually runs
# the program.
# ###########################################################################
package mysql_msr;

use strict;
use warnings FATAL => 'all';
use Getopt::Long;
use Pod::Usage;
use POSIX qw(setsid floor ceil strftime);
use IO::Handle;
use English qw(-no_match_vars);
use FindBin qw($RealBin);
Log->import();

use constant EZDEBUG => $ENV{EZDEBUG} || 0;
use constant MYSQLBINLOG_MIN_VER => 3.2;

our $VERSION = '@VERSION@';
our $SVN_REV = sprintf("%d", (q$Revision: $ =~ m/(\d+)/g, 0));

my $stop = 0;
my $pidfile = "/var/run/$0.pid";

# {{{ process functions
sub readpid
{
	my $p = -1;
	if (-e $pidfile and open(PF, $pidfile))
	{
		$p = <PF>;
		chomp($p);
		close PF;
	}
	return $p;
}

# Stop properly
sub do_stop
{
	my $sig = shift;
	# do nothing if already stopping
	#return 0 if ($stop);

	if ($sig eq "HUP")
	{
		$stop = 2;
	}
	else
	{
		_i("Exiting $0 ($sig) ...");
		$stop = 1;
	}
}

# Arrete l'instance lancé si existante
sub do_shutdown
{
	my $exit = shift || 0;
	if (-e $pidfile)
	{
		my $p = readpid;
		if ($p and kill 0, $p)
		{
			_i('-n', "Shutting down... ");
			kill 15, $p;
			sleep(1);
			if (kill 0, $p)
			{
				_i('-n', "forcing... ");
				kill 9, $p;
			}
			if (kill 0, $p)
			{
				_i("FAILED!");
			}
			else
			{
				_i("OK.");
			}
			_d("removing pid file $pidfile.");
			unlink ($pidfile) if (-e $pidfile);
		}
	}
	exit if ($exit);
}


# daemonize via double fork
sub daemonize
{
	# First fork
	if (fork)
	{
		#print "FIN DU PERE\n";
		exit 0;
	}
	
	
	# Redirecting input and output to /dev/null
	open STDIN, '/dev/null' or die "Can't read /dev/null: $!";
	open STDOUT, '>/dev/null';
	open STDERR, '>/dev/null';
	setsid;
	
	# Second fork, daemon isn t related anymore to the terminal.
	if (fork)
	{
		#print "FIN DU PERE 2\n";
		exit 0;
	}
	
	chdir '/tmp' or die "Can't chdir to /tmp: $!";
}

sub is_running
{
	# check if already running
	if (-e $pidfile)
	{
		my $p = readpid;
		# killable ?
		if ($p and kill (0, $p) > 0)
		{
			_i("Already running, exit.");
			return 1;
		}
	}
	return 0;
}
# }}}


#
# Setup
#
sub setup
{
	my ($config) = @_;
	$config->{management}->{setup} = 1;
	my $mgr = new SlaveManager($config);
	return $mgr->setup_db();
}

# 
# Nagios compatibles checks
#
sub checks
{
	my ($config) = @_;
	use constant NAGIOS_EXIT_CODES => {'OK'=>0,'WARNING'=>1,'CRITICAL'=>2,'UNKNOWN'=>3,'DEPENDENT'=>4};
	my ($enabled, $ioalive, $sqlalive, $count, $relaylate, $norelaylog, $onioerror, $onsqlerror) = (0, 0, 0, 0, 0, 0, 0, 0);
	my $bigpause = defined($config->{general}{bigpause}) ? $config->{general}{bigpause} : 10;
	my $mgr = new SlaveManager($config);

	my $slaves = $mgr->slaves(0);
	sleep $bigpause + 1; # /!\ warning to nagios timeout /!\
	my $slaves2 = $mgr->slaves(0);

	# check childs status
	foreach my $slave (keys %$slaves2)
	{
		$count++;
		$enabled++ if ($slaves2->{$slave}->{enabled});
		if ($STATUS[$slaves2->{$slave}->{io_status}] =~ /^error/)
		{
			$onioerror++;
		}
		if ($STATUS[$slaves2->{$slave}->{sql_status}] =~ /^error/)
		{
			$onsqlerror++;
		}
		$ioalive++ if ($slaves2->{$slave}->{io_status} > 0 or $slaves2->{$slave}->{io_status} != $slaves->{$slave}->{io_status});
		$sqlalive++ if ($slaves2->{$slave}->{sql_status} or $slaves2->{$slave}->{sql_status} != $slaves->{$slave}->{sql_status});
		# check relaylogs
		$relaylate += scalar(keys %{$mgr->get_relay_logs($slaves2->{$slave})});
		# check bug undefined relaylogs
		$norelaylog = $slaves2->{$slave}->{master_id} if ($slaves2->{$slave}->{sql_status} == 10);
	}

	$relaylate = int($relaylate/$enabled) if ($relaylate and $enabled);

	print "Master $norelaylog has no logs, " if ($norelaylog);
	print $relaylate." avg relay logs, $ioalive/$enabled IO, $sqlalive/$enabled SQL, $enabled/$count enabled, $onioerror/$onsqlerror IO/SQL errors$/";
	if ($ioalive < $enabled or $sqlalive < $enabled or $enabled < $count or $relaylate > 40 or $onioerror > 0 or $onsqlerror > 0)
	{
		return NAGIOS_EXIT_CODES->{CRITICAL};
	}
	elsif ($enabled < $count or $relaylate > 10 or $norelaylog > 0)
	{
		return NAGIOS_EXIT_CODES->{WARNING};
	}
	else
	{
		return NAGIOS_EXIT_CODES->{OK};
	}

}

#
# Configure slaves : add, remove, change
#
sub slave_config
{
	my ($config, $slavedef) = @_;
	_d("Slave mode");
	my $mgr = new SlaveManager($config);
	my $action;

	$action = 'add' if ($slavedef->{add});
	$action = 'remove' if ($slavedef->{remove});
	$action = 'change' if ($slavedef->{change});
	$action = 'disable' if ($slavedef->{disable});
	$action = 'enable' if ($slavedef->{enable});
	$action = 'skip' if ($slavedef->{skip});
	$slavedef->{name} = $slavedef->{$action};
	
	return $mgr->$action($slavedef);

}


sub replication_loop
{
	my ($configfile) = @_;
	my $config = ConfigIni::parse_ini($configfile);
	# 
	# Fetch slaves configuration
	#
	my $mgr = new SlaveManager($config);
	my %replicators;

	# 
	# Loop
	#
	my $no_more_slave_warned = 0;
	while (!$stop)
	{
		$config = ConfigIni::parse_ini($configfile);
		my $bigpause = defined($config->{general}{bigpause}) ? $config->{general}{bigpause} : 10;
		my @slaves = $mgr->list_slaves(1);
		if (@slaves)
		{
			$no_more_slave_warned = 0;
			for my $name (@slaves)
			{
				unless(defined($replicators{$name}))
				{
					$mgr->print_slave($name);
					$replicators{$name} = new Slave($configfile, $name);
				}

				unless($replicators{$name}->is_alive() == 2)
				{
					delete $replicators{$name} if ($replicators{$name}->stop());
					@slaves = $mgr->list_slaves(1);
				}
			}
			#sleep $bigpause;
			sleep 1;
		}
		else
		{
			_err("No more slave alived...") unless ($no_more_slave_warned);
			$no_more_slave_warned = 1;
			sleep $bigpause;
		}
	}

	# 
	# Stop
	#
	foreach my $child (keys %replicators)
	{
		delete $replicators{$child} if ($replicators{$child}->stop());
	}
	return 0;
}



#
# MAIN
#
sub main 
{
	#
	# vars declaration
	#
	@ARGV = @_;  # set global ARGV for this package
	my $daemon = 0;
	my $configfile;
	my $config;
	my $verbose = 1;
	my %slave;
	my $checks = 0;
	my $setup = 0;
	
	#
	# Get configuration information.
	#
	GetOptions( 
		"h|help" => sub { pod2usage(1); },
		"c|config=s" => \$configfile,
		"daemon" => \$daemon,
		"pidfile=s" => \$pidfile,
		"v|verbose+" => \$verbose,
		"a|add=s" => \$slave{add},
		"r|remove=s" => \$slave{remove},
		"change=s" => \$slave{change},
		"skip=s" => \$slave{skip},
		"offset=i" => \$slave{offset},
		"user=s" => \$slave{user},
		"password=s" => \$slave{password},
		"H|host=s" => \$slave{host},
		"P|port=s" => \$slave{port},
		"S|sock=s" => \$slave{sock},
		"pos=s" => \$slave{pos},
		"binlogfile=s" => \$slave{binlogfile},
		"enable=s" => \$slave{enable},
		"disable=s" => \$slave{disable},
		"checks" => \$checks,
		"setup" => \$setup,
	) or pod2usage(2);

	# 
	# Starting infos
	#
	my ($program_name) = $PROGRAM_NAME =~ m/([.A-Za-z-_0-9]+)$/;
	$program_name ||= $PROGRAM_NAME;
	my $home = $ENV{HOME} || $ENV{HOMEPATH} || $ENV{USERPROFILE} || '.';

	
	# 
	# Read config
	#
	#$configfile = "$home/msr.ini" unless ($configfile);
	$configfile = "$RealBin/../conf/msr.ini" unless ($configfile);
	$config = ConfigIni::parse_ini($configfile);

	#
	# Logger
	#
	Log->new(
		file => $config->{general}{logfile},
		verbose => "$verbose/5",
		daemon => $daemon,
		cosmetic => 'x',           		#crosses for the level
		#colors => {'prog' => 'white', 'date' => 'yellow' },
		colors => !$daemon,
		error_header => '', 		#Header for true errors
		header => '%dd %l[]l %s{}s ',	#The header
		splash => 1,
		caller => EZDEBUG ? 'all' : 0);            		#and I want the name of the last sub

	#
	# Checks mode ?
	#
	return checks($config) if ($checks);

	#
	# Setup Mode
	#
	return setup($config) if ($setup);

	#
	# Slave mode ?
	#
	return slave_config($config, \%slave) if ($slave{add} or $slave{remove} or $slave{change} or $slave{skip} or $slave{enable} or $slave{disable});


	_l(1,"Starting...");


	# 
	# Check mysqlbinlog version >= 3.3
	#
	# /usr/local/mysql/bin/mysqlbinlog --no-defaults -V
	# /usr/local/mysql/bin/mysqlbinlog Ver 3.3 for unknown-linux-gnu at x86_64
	my $mysqlbin = defined($config->{general}{mysqlbin}) ? $config->{general}{mysqlbin} : '/usr/local/mysql/bin';
	my $mysqlbinlogversion = `$mysqlbin/mysqlbinlog --no-defaults -V`;
	$mysqlbinlogversion =~ /Ver (\d+.\d+) /;
	$mysqlbinlogversion = $1;
	unless ($mysqlbinlogversion >= MYSQLBINLOG_MIN_VER)
	{
		_err("Need mysqlbinlog version >= ".MYSQLBINLOG_MIN_VER);
		exit 1;
	}

	#
	# Please exit properly...
	#
	local $SIG{TERM} = $SIG{INT} = $SIG{HUP} = \&do_stop;
	# Change program name
	($0, undef, undef) = caller 0;

	# 
	# Daemon
	#
	if ($daemon)
	{	
		_l(1,"Daemonize...");
		# Check write access
		unless (open(PF, ">$pidfile"))
		{
			_err("Can't write to pidfile $pidfile: $!");
			die "Can't write to pidfile $pidfile: $!\n";
		}
		close PF;

		daemonize();

		# really write pid file (after daemonize!)
		if (open(PF, ">$pidfile"))
		{
			print PF $$;
			close PF;
		}
	}

	#
	# Replication loop
	#
	my $exitcode = replication_loop($configfile);


	_l(1,"Done.");
	if ($daemon and -e $pidfile)
	{
		_d("Removing pidfile $pidfile");
		unlink ($pidfile) if (-e $pidfile);
	}
	return $exitcode;
}

##############################################################################
## Run the program.
##############################################################################
if ( !caller ) 
{ 
	use File::Basename;
	$0 = File::Basename::basename($0, ".pl");
	exit main(@ARGV); 
}

1; # Because this is a module as well as a script.

# ############################################################################
# Documentation.
# ############################################################################

=pod

=head1 NAME

mysql_msr.pl - Do multiple sources replication with mysqlbinlog tool

=head1 SYNOPSIS

   mysql_msr.pl ....

=head1 OPTIONS

=over

=item1 --setup

Setup database and tables.
Setup will connect to the destination MySQL server, create the database and the necessary tables if not exists.

=item1 --checks

Do some checks compatible with Nagios

=item --nodaemon

Keep in foreground, do not daemonize

=item --pidfile

type: string

Write pidfile to this file, useful for start-stop-daemon.

=item --config

type: Array

Read this INI config file.

=item --verbose, -v

Increment verbosity, between 1 (default) and 5 (max).

=head1 SLAVE MODE OPTIONS

Used to configure a slave: add, remove or change a slave.

=over

=item1 --add slave_name

Name of the new slave

=item1 --remove slave_name

Name of the slave to remove

=item1 --change slave_name

Name of the slave to change

=item1 --skip slave_name

Name of the slave to change

==item1 --user username

MySQL username to connect with

==item1 --password the_big_password

MySQL password in conjunction with username

==item1 --host hostname_or_IP

MySQL hostname or IP

==item1 --port port_number

MySQL port

==item1 --sock socket

MySQL socket if running on the same server

==item1 --pos NNNNN

The current binlog position of this slave.

==item1 --binlogfile mysql-bin.000123

The current binlog file of this slave.

==item1 --disable, --enable

Disable (aka STOP SLAVE) or enable the slave.

=head1 AUTHOR

Grégory Duchatelet

=head1 VERSION

This manual page documents Ver @VERSION@ $Revision: $.

=cut
