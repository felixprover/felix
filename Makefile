all: test lib

DEPLOY_DEST ?= vps:/var/www/naproche.org/
RSYNC_FLAGS ?= -az --delete-delay --itemize-changes --exclude=".DS_Store"
# Capture origin before installing the shared fallback: lib distinguishes an
# explicit shorthand from the executable's automatic component defaults.
FELIX_JOBS_ORIGIN := $(origin FELIX_JOBS)
FELIX_JOBS ?= 8
# Stack reads stack.yaml (O2) by default. STACK_YAML selects another configuration
# consistently for builds, execution, and helper scripts; do not switch -O flags.
STACK_BUILD_FLAGS ?=
FELIX_VERIFY_FLAGS ?=
# Resolve aliases before recipes (and parallel prerequisite builds) can run.
VERIFY_POLICIES := $(sort $(filter lib lib-refresh spike spike-refresh,$(MAKECMDGOALS)) $(if $(filter all,$(or $(MAKECMDGOALS),all)),lib))
ifneq ($(word 2,$(VERIFY_POLICIES)),)
$(error Select one verification policy per invocation: $(VERIFY_POLICIES))
endif
FELIX_STORE ?= $(if $(filter spike spike-refresh,$(VERIFY_POLICIES)),.cache/spike.sqlite,.cache/library.sqlite)
# Quote literal values for the shell; the validator parses flags without eval.
shell_quote = '$(subst ','"'"',$(1))'
ifneq ($(VERIFY_POLICIES),)
VERIFY_FLAGS_ERROR := $(shell perl tools/verification-command.pl check $(call shell_quote,$(FELIX_VERIFY_FLAGS)) || echo 'Cannot validate FELIX_VERIFY_FLAGS')
ifneq ($(VERIFY_FLAGS_ERROR),)
$(error $(VERIFY_FLAGS_ERROR))
endif
ifeq ($(strip $(FELIX_STORE)),)
$(error FELIX_STORE must name a verification store)
endif
endif

LIBRARY_ROOT := library/everything.tex
LIBRARY_SPIKE := library/topology/urysohn/chain.tex
LIBRARY_PROFILE := library/topology/urysohn/chain.tex
SOURCE_SCAN_ROOT := $(abspath $(LIBRARY_PROFILE))
PROFILE_DIR := profiling
# Override on the make command line for short, deeply instrumented probes.
PROFILE_GHC_OPTIONS := -fprof-late -fno-prof-count-entries
PROFILE_RTS_OPTION := -P
PROFILE_FORMAT := ghc-text
PROFILE_CACHE_FLAGS ?= --refresh
PROFILE_STORE ?= .cache/store.sqlite
PROFILE_RTS_FLAGS ?=
TIMED_COMMAND := benchmark/run-timed.sh

# The spike is a representative iteration slice; lib covers the full graph,
# while lib-refresh records elapsed time only after successful verification.
.PHONY: spike spike-refresh lib lib-refresh
spike spike-refresh: LIBRARY_TARGET := $(LIBRARY_SPIKE)
spike spike-refresh: LIBRARY_JOBS = --jobs "$(FELIX_JOBS)"
lib lib-refresh: LIBRARY_TARGET := $(LIBRARY_ROOT)
lib-refresh: LIBRARY_TIME_LOG := $(PROFILE_DIR)/everything.time
lib lib-refresh: LIBRARY_JOBS = $(if $(filter undefined,$(FELIX_JOBS_ORIGIN)),,--jobs "$(FELIX_JOBS)")
spike lib: LIBRARY_POLICY := reuse
spike-refresh lib-refresh: LIBRARY_POLICY := refresh
spike lib: LIBRARY_CACHE_FLAGS = --store $(call shell_quote,$(FELIX_STORE))
spike-refresh lib-refresh: LIBRARY_CACHE_FLAGS = --store $(call shell_quote,$(FELIX_STORE)) --refresh
spike spike-refresh lib lib-refresh:
	stack build $(STACK_BUILD_FLAGS)
	@printf 'Verifying %s; store %s; policy %s\n' "$(LIBRARY_TARGET)" $(call shell_quote,$(FELIX_STORE)) "$(LIBRARY_POLICY)"; \
	if test -n "$(LIBRARY_TIME_LOG)"; then \
		timestamp="$$(date +%y%m%d_%H%M)"; \
		mkdir -p "$(dir $(LIBRARY_TIME_LOG))"; \
		$(TIMED_COMMAND) elapsed-log "$(LIBRARY_TIME_LOG)" "$$timestamp" -- \
			perl tools/verification-command.pl exec $(call shell_quote,$(FELIX_VERIFY_FLAGS)) \
				"$(LIBRARY_TARGET)" $(LIBRARY_CACHE_FLAGS) --check-render-hints -t 20 $(LIBRARY_JOBS); \
	else \
		time perl tools/verification-command.pl exec $(call shell_quote,$(FELIX_VERIFY_FLAGS)) \
			"$(LIBRARY_TARGET)" $(LIBRARY_CACHE_FLAGS) --check-render-hints -t 20 $(LIBRARY_JOBS); \
	fi

.PHONY: dump
dump:
	stack build $(STACK_BUILD_FLAGS)
	@dump_dir="$(DUMP_DIR)"; \
	if test -z "$$dump_dir"; then \
		dump_dir="$$(mktemp -d "$${TMPDIR:-/tmp}/felix-dump.XXXXXX")"; \
	fi; \
	printf 'Writing dump to %s\n' "$$dump_dir"; \
	time stack exec felix -- --fresh "$(LIBRARY_ROOT)" -t 17 \
		--jobs "$(FELIX_JOBS)" --dump "$$dump_dir"

.PHONY: build build-fast
build:
	stack build $(STACK_BUILD_FLAGS)

build-fast:
	stack --stack-yaml stack-fast.yaml build $(STACK_BUILD_FLAGS)

.PHONY: test test-fast test-acceptance golden test-build check-boundaries \
	check-imports check-api check-obvious-bridge check-tools
test test-fast test-acceptance: check-boundaries check-obvious-bridge
test:
	stack test $(STACK_BUILD_FLAGS)

test-fast:
	stack test $(STACK_BUILD_FLAGS) --test-arguments "-p fast"

test-acceptance:
	stack test $(STACK_BUILD_FLAGS) --test-arguments "-p acceptance"

test-build:
	stack test $(STACK_BUILD_FLAGS) --no-run-tests

check-boundaries: check-imports check-api

check-imports:
	@bash test/check-import-checks.sh
	@bash test/check-imports.sh

check-api: test-build
	@stack exec -- bash test/check-api.sh

check-obvious-bridge: test-build
	@sh test/check-obvious-bridge.sh

check-tools:
	bash tools/test-library-command.sh
	python3 -B tools/test_atp_compare.py
	bash tools/test-runtime-defaults.sh

golden:
	stack test $(STACK_BUILD_FLAGS) --test-arguments "--accept -p golden"

.PHONY: bench-parser
bench-parser:
	stack build $(STACK_BUILD_FLAGS) felix:lib felix:bench:parser-bench --no-run-benchmarks
	@printf '%s\n' 'See benchmark/parser/readme.md for isolated correctness and comparison commands.'

.PHONY: bench-source-scan bench-source-scan-space bench-source-scan-e2e \
	record-source-scan-surface
bench-source-scan:
	stack build $(STACK_BUILD_FLAGS) felix:bench:source-scan-bench --no-run-benchmarks
	@helper="$$(realpath \
		"$$(stack path --dist-dir)/build/source-scan-bench/source-scan-bench")"; \
	"$$helper" criterion "$(SOURCE_SCAN_ROOT)" $(CRITERION_OPTIONS)

bench-source-scan-space:
	stack build $(STACK_BUILD_FLAGS) felix:bench:source-scan-bench --no-run-benchmarks
	@helper="$$(realpath \
		"$$(stack path --dist-dir)/build/source-scan-bench/source-scan-bench")"; \
	SOURCE_SCAN_BUILD_COMMAND="STACK_YAML=$${STACK_YAML:-stack.yaml} stack build $(STACK_BUILD_FLAGS) felix:bench:source-scan-bench --no-run-benchmarks" \
	benchmark/source-scan/run-space.sh \
		"$$helper" "$(SOURCE_SCAN_ROOT)" "$(SOURCE_SCAN_SPACE_OUTPUT)"

bench-source-scan-e2e:
	@test -n "$(BASELINE_FELIX)" || \
		{ printf '%s\n' 'BASELINE_FELIX is required'; exit 2; }
	@test -n "$(BASELINE_SOURCE_SCAN_BENCH)" || \
		{ printf '%s\n' 'BASELINE_SOURCE_SCAN_BENCH is required'; exit 2; }
	@test -n "$(BASELINE_REVISION)" || \
		{ printf '%s\n' 'BASELINE_REVISION is required'; exit 2; }
	@test -n "$(BASELINE_BUILD_COMMAND)" || \
		{ printf '%s\n' 'BASELINE_BUILD_COMMAND is required'; exit 2; }
	stack build $(STACK_BUILD_FLAGS) felix:exe:felix felix:bench:source-scan-bench \
		--no-run-benchmarks
	@candidate_felix="$$(stack exec -- which felix)"; \
	candidate_helper="$$(realpath \
		"$$(stack path --dist-dir)/build/source-scan-bench/source-scan-bench")"; \
	BASELINE_REVISION="$(BASELINE_REVISION)" \
	CANDIDATE_REVISION="$$(git rev-parse HEAD)" \
	BASELINE_BUILD_COMMAND="$(BASELINE_BUILD_COMMAND)" \
	CANDIDATE_BUILD_COMMAND="STACK_YAML=$${STACK_YAML:-stack.yaml} stack build $(STACK_BUILD_FLAGS) felix:exe:felix felix:bench:source-scan-bench --no-run-benchmarks" \
	NAPROCHE_LIB="$(abspath library)" \
	benchmark/source-scan/run-e2e.sh \
		"$(BASELINE_FELIX)" "$$candidate_felix" \
		"$(BASELINE_SOURCE_SCAN_BENCH)" "$$candidate_helper" \
		"$(SOURCE_SCAN_ROOT)" "$(SOURCE_SCAN_E2E_OUTPUT)"

record-source-scan-surface:
	benchmark/source-scan/record-production-surface.sh \
		"$(or $(SOURCE_SCAN_REVISION),HEAD)"

.PHONY: publish
publish:
	rsync $(RSYNC_FLAGS) html/ $(DEPLOY_DEST)

PROFILE_TARGETS := profilebaseline profile profileall profilejson profilewarm profilemem profileparser
.PHONY: $(PROFILE_TARGETS)
profileall profilewarm profileparser: LIBRARY_PROFILE := $(LIBRARY_ROOT)
profilejson: PROFILE_RTS_OPTION := -pj
profilejson: PROFILE_FORMAT := ghc-json
$(PROFILE_TARGETS):
	@LIBRARY_PROFILE=$(call shell_quote,$(LIBRARY_PROFILE)) \
	PROFILE_DIR=$(call shell_quote,$(PROFILE_DIR)) \
	PROFILE_GHC_OPTIONS=$(call shell_quote,$(PROFILE_GHC_OPTIONS)) \
	PROFILE_RTS_OPTION=$(call shell_quote,$(PROFILE_RTS_OPTION)) \
	PROFILE_FORMAT=$(call shell_quote,$(PROFILE_FORMAT)) \
	PROFILE_CACHE_FLAGS=$(call shell_quote,$(PROFILE_CACHE_FLAGS)) \
	PROFILE_STORE=$(call shell_quote,$(PROFILE_STORE)) \
	PROFILE_RTS_FLAGS=$(call shell_quote,$(PROFILE_RTS_FLAGS)) \
	FELIX_JOBS=$(call shell_quote,$(FELIX_JOBS)) \
	FELIX_VERIFY_FLAGS=$(call shell_quote,$(FELIX_VERIFY_FLAGS)) \
	STACK_BUILD_FLAGS=$(call shell_quote,$(STACK_BUILD_FLAGS)) \
	bash tools/profile.sh "$@"
