#!/usr/bin/env bash

##  running `produceSed <build_log>` on the build log produces a list of sed commands
##  that replace all doc-string-less `theorem`s by `lemma`s.
produceSed () {
  if [ -z "${2}" ]
  then
    sh=2
  else
    sh="${2}"  ##  if parsing the downloaded logs, set `sh` to `4`
  fi
  awk -F: -v ti="'" -v sh="${sh}" '($(sh) ~ /^ \.\//){
    fil=$(sh); gsub(/\.\//, "", fil); row=$(sh+1); col=$(sh+2); gsub(/-.*/, "", col)
    fils[fil]=fils[fil] ":" row "-" col
  } END{
    for(fil in fils){
      printf("sed -i %s\n", ti)
      split(fils[fil], pos, ":")
      for(p in pos) { if(pos[p] != ""){
        split(pos[p], rc, "-")
        printf("  %s{s=\\(.\\{%s\\}\\)\\(theorem\\)=\\1lemma=}\n", rc[1], rc[2])
      }}
      printf("%s%s\n", ti, fil)
    }
  }' "${1}"
}

#eval "$(lake build | produceSed -)"