SRC_DIRS := 'src' 'new'
# ALL_VFILES is used to calculate dependencies
ALL_VFILES := $(shell find $(SRC_DIRS) \
	-type f -not -name "*__nobuild.v" -name "*.v")
# PROJ_VFILES is for the all target
PROJ_VFILES := $(shell find src new \
	-not -path "*/*__nobuild/*" -a \
	-not -name "*__nobuild.v" -name "*.v")

# extract any global arguments for Rocq from _RocqProject
ROCQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _RocqProject)
ROCQ_ARGS :=
# rocqdep: don't allow missing files
ROCQ_DEP_ARGS := -w +module-not-found

# user configurable
Q:=@
TIMED:=true
TIMING_DB:=.timing.sqlite3
# Seconds a file must take before the build prints its time. 0 prints every
# file; `make TIMING_MIN=10 ...` prints only the slow ones.
TIMING_MIN:=0
# Extra flags for `make timing-report`, e.g. TIMING_REPORT_ARGS="--mode vok"
TIMING_REPORT_ARGS:=
# Extra flags for the report `make ci` prints and for `make build-report`,
# e.g. BUILD_REPORT_ARGS="--markdown-to $GITHUB_STEP_SUMMARY" in CI
BUILD_REPORT_ARGS:=

# One id per top-level `make` run, with its start time and goals: etc/rocqc.py
# files every compile under it, which is what lets etc/build-report.py tell
# this build from earlier ones in $(TIMING_DB). A sub-make inherits the
# parent's (the variables are exported, so their origin there is `environment`).
ifeq ($(origin ROCQ_BUILD_ID),undefined)
ROCQ_BUILD_ID := $(shell date -u +%Y%m%dT%H%M%SZ)-$(shell od -An -N3 -tx1 /dev/urandom | tr -d ' \n')
ROCQ_BUILD_START := $(shell date +%s.%N)
ROCQ_BUILD_GOALS := $(MAKECMDGOALS)
endif
export ROCQ_BUILD_ID ROCQ_BUILD_START ROCQ_BUILD_GOALS

-include Makefile.test

# We detect Rocq CI via the TIMING variable (used in coq_makefile) and then
# disable the rocqc.py wrapper, which doesn't work there
ifneq (,$(TIMING))
ROCQ_C := rocq compile
else ifeq ($(TIMED), true)
ROCQ_C := ./etc/rocqc.py --timing-db $(TIMING_DB) --print-time $(TIMING_MIN)
else
# setting TIMED to false or the empty string will disable using the wrapper,
# for environments where it doesn't work
ROCQ_C := rocq compile
endif

default: all

all: $(PROJ_VFILES:.v=.vo)
vos: $(PROJ_VFILES:.v=.vos)
vok: $(PROJ_VFILES:.v=.vok)

.PHONY: new-goose new-goose.vos
new-goose:
	$(Q)$(MAKE) $$(./etc/package-sources.sh new-goose | sed 's/\.v$$/\.vo/')
new-goose.vos:
	$(Q)$(MAKE) $$(./etc/package-sources.sh new-goose | sed 's/\.v$$/\.vos/')

.rocqdeps.d: $(ALL_VFILES) _RocqProject
	@echo "ROCQ DEP $@"
	$(Q)rocq dep -vos -f _RocqProject $(ROCQ_DEP_ARGS) $(ALL_VFILES) > $@

# do not try to build dependencies if cleaning or just building _RocqProject
ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include .rocqdeps.d
endif

# implement coq_makefile's TIMING support for Rocq CI
ifneq (,$(TIMING))
TIMING_ARGS=-time
TIMING_EXT?=timing
TIMING_EXTRA = > $<.$(TIMING_EXT)
endif


%.vo: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ COMPILE $<"
	$(Q)$(ROCQ_C) $(ROCQPROJECT_ARGS) $(ROCQ_ARGS) $(TIMING_ARGS) -o $@ $< $(TIMING_EXTRA)

%.vos: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ COMPILE -vos $<"
	$(Q)$(ROCQ_C) $(ROCQPROJECT_ARGS) -vos $(ROCQ_ARGS) $< -o $@

%.vok: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ COMPILE -vok $<"
	$(Q)$(ROCQ_C) $(ROCQPROJECT_ARGS) $(TIMING_ARGS) -vok $(ROCQ_ARGS) $< -o $@

.PHONY: skip-qed unskip-qed ci

SLOW_QED_FILES := ""

skip-qed:
	$(Q)./etc/disable-qed.sh $(SLOW_QED_FILES)

unskip-qed:
	$(Q)./etc/disable-qed.sh --undo $(SLOW_QED_FILES)

# What CI checks: new/should_build.vo, then a report of that build (time,
# parallelism over time, critical path, slowest files; etc/build-report.py).
# The build runs as a sub-make so that the report is printed even when it
# fails; `make ci` exits with the build's status either way. Without the
# rocqc.py wrapper (TIMED=false, or Rocq CI's TIMING) nothing is recorded, so
# there is no report.
ifeq ($(ROCQ_C),rocq compile)
CI_REPORT := true
else
CI_REPORT := ./etc/build-report.py --db $(TIMING_DB) --build $(ROCQ_BUILD_ID) $(BUILD_REPORT_ARGS) \
	|| echo "build-report failed (the build's own status is unaffected)" >&2
endif

ci:
	$(Q)rc=0; $(MAKE) --no-print-directory new/should_build.vo || rc=$$?; \
	echo; $(CI_REPORT); exit $$rc

# The report `make ci` prints, for the latest build recorded in $(TIMING_DB)
# -- whatever its goals. `./etc/build-report.py --list` lists them all.
.PHONY: build-report
build-report:
	$(Q)./etc/build-report.py --db $(TIMING_DB) $(BUILD_REPORT_ARGS)

# Where the last build spent its time. Each build mode is reported
# separately, since a file's vo, vos and vok builds cost different amounts.
.PHONY: timing-report
timing-report:
	$(Q)./etc/timing-report.py --db $(TIMING_DB) $(TIMING_REPORT_ARGS)

# compiled by Rocq CI
# not intended for normal development
lite: src/LiteBuild.vo

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIRS) tests \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -o -name "*.glob" \) -delete
	$(Q)rm -f .lia.cache
	$(Q)rm -f $(TIMING_DB)
	rm -f .rocqdeps.d tests/.rocqdeps.d

.PHONY: default
.DELETE_ON_ERROR:
