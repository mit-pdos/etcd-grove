#!/bin/bash
# Summarize results.txt (run.sh's output): per case, mode (sys: one unix.Pwrite; go: os.File.WriteAt)
# and result (nil / errno), how much of the write the page cache holds afterwards (none, partial,
# full), where a partial prefix ends (mod 4096), whether it equals the returned count, and the
# pattern bytes found beyond it.
awk '/^== /{sec=$2} / sys off=| go  off=/{
  for(i=1;i<=NF;i++){
    if($i ~ /^len=/){split($i,a,"=");l=a[2]}
    if($i ~ /^n=/){split($i,b,"=");n=b[2]}
    if($i ~ /^landed=/){split($i,c,"=");p=c[2]}
    if($i ~ /^beyond=/){split($i,d,"=");bz=d[2]}
    if($i ~ /^\(off\+landed\)%4096=/){split($i,e,"=");pe=e[2]} }
  mode=($0 ~ / sys off=/)?"sys":"go"; err=($0 ~ /err=nil/)?"nil":"errno"
  key=sec" "mode" "err" landed:"((p==0)?"none":(p<l)?"partial":"full")" end%4096="((p>0&&p<l)?pe:"-")" landed==n:"((p==n)?"y":"n")" beyond="bz
  cnt[key]++ } END {for(k in cnt) print cnt[k], k}' "${1:-$(dirname "$0")/results.txt}" | sort -k2
