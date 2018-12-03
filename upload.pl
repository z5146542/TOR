#!/usr/bin/perl -w

use strict;
use warnings;

my $date = `date`;
chomp $date;

print `git status` and  print `git add .` and print `git status` and print `git commit -m "worked at $date"` and print `git status` and print `git push` and print `git status`;
