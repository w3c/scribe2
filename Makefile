all: regressionTests

# REGRESSION TESTS
#
# Each test is an executable with a name ending in .test. It must exit
# with status code 0 (test succeeded), 2 (test not applicable) or any
# other code (test failed). Any output is captured in a log file.

TESTS := $(wildcard tests/*.test)
RESULTS := $(TESTS:.test=.result)

ECHO=/bin/echo

# Terminal escape codes for red, green and blue
FAIL := $(shell tput setaf 1)FAIL$(shell tput op)
OK := $(shell tput setaf 2)OK$(shell tput op)
NA := $(shell tput setaf 4)N/A$(shell tput op)

%: %.test scribe.perl
	@$(ECHO) -n $< ""
	@$< >$*.log 2>&1; \
	 case $$? in \
	 0) $(ECHO) "$(OK)"; $(ECHO) OK >$*.result;; \
	 2) $(ECHO) "$(NA)"; $(ECHO) N/A >$*.result;; \
	 *) $(ECHO) "$(FAIL)"; $(ECHO) FAIL >$*.result;; \
	 esac

regressionTests: $(TESTS:.test=)
	@$(ECHO) "===================="
	@$(ECHO) "$(OK)  " `grep OK $(RESULTS) | wc -l`
	@$(ECHO) "$(FAIL)" `grep FAIL $(RESULTS) | wc -l`
	@$(ECHO) "$(NA) " `grep N/A $(RESULTS) | wc -l`
