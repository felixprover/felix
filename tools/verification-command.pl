#!/usr/bin/env perl
use strict;
use warnings;

my ($mode, $flags, @fixed) = @ARGV;
die "Expected check, args, or exec, flags, and optional fixed arguments\n"
    unless defined($flags) && ($mode eq 'check' || $mode eq 'args' || $mode eq 'exec');

sub reject {
    my ($message) = @_;
    # Make captures check-mode stdout before any prerequisites can run.
    my $stream = $mode eq 'check' ? \*STDOUT : \*STDERR;
    print {$stream} "$message\n";
    exit 2;
}

reject('FELIX_VERIFY_FLAGS must contain literal arguments, not shell expansions')
    if $flags =~ /[\$`\r\n]/;

# Accept whitespace-separated words with shell quoting, but no shell evaluation.
# Quoted fragments concatenate; empty quotes still produce an argument.
my @optional;
pos($flags) = 0;
while (1) {
    $flags =~ /\G[ \t]*/gc;
    last if pos($flags) == length($flags);
    my $word = '';
    my $start = pos($flags);
    while ($flags =~ /\G(?:'([^']*)'|"((?:[^"\\]|\\.)*)"|\\(.)|([^ \t'"\\;&|<>()]+))/gc) {
        if (defined $1) {
            $word .= $1;
        } elsif (defined $2) {
            my $quoted = $2;
            $quoted =~ s/\\(["\\])/$1/g;
            $word .= $quoted;
        } else {
            $word .= defined($3) ? $3 : $4;
        }
    }
    reject('Invalid FELIX_VERIFY_FLAGS: expected literal, shell-quoted arguments')
        if pos($flags) == $start || $word =~ /\A(?:\#|[;&|<>()]+\z)/;
    reject('Use FELIX_STORE and the verification target to select store policy')
        if $word =~ /\A(?:--store(?:=.*)?|--refresh|--fresh)\z/;
    push @optional, $word;
}

if ($mode eq 'args') {
    print "$_\0" for @optional;
} elsif ($mode eq 'exec') {
    exec {'stack'} 'stack', 'exec', '--', 'felix', @fixed, @optional;
    die "Cannot execute stack: $!\n";
}
