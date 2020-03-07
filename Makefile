all: check samples

# REGRESSION TESTS
#
# Each test is an executable with a name ending in .test. It must exit
# with status code 0 (test succeeded), 2 (test not applicable) or any
# other code (test failed). Any output is captured in a log file.

TESTS := $(sort $(wildcard tests/*.test))
RESULTS := $(TESTS:.test=.result)

ECHO=/bin/echo

# Terminal escape codes for red, green and blue
CLR_EOL := $(shell tput el)
FAIL := $(shell tput setaf 1)FAIL$(shell tput op)
OK := $(shell tput setaf 2)OK$(shell tput op)
NA := $(shell tput setaf 4)N/A$(shell tput op)

%: %.test scribe.perl
	@$< >$*.log 2>&1; \
	 case $$? in \
	 0) $(ECHO) -n "$< $(OK)$(CLR_EOL)"; $(ECHO) OK >$*.result;; \
	 2) $(ECHO) -n "$< $(NA)$(CLR_EOL)"; $(ECHO) N/A >$*.result;; \
	 *) $(ECHO) "$< $(FAIL)$(CLR_EOL)"; $(ECHO) FAIL >$*.result;; \
	 esac

check: $(TESTS:.test=)
	@$(ECHO) "====================$(CLR_EOL)"
	@$(ECHO) "$(OK)  " `grep OK $(RESULTS) | wc -l`
	@$(ECHO) "$(FAIL)" `grep FAIL $(RESULTS) | wc -l`
	@$(ECHO) "$(NA) " `grep N/A $(RESULTS) | wc -l`

# SAMPLES
#
# Update the sample minutes whenever scribe.perl changes

samples: sample-public.html sample-member.html sample-team.html \
	sample-fancy.html
sample-public.html: sample-public.txt scribe.perl
	perl scribe.perl --final --embed $< >$@
sample-member.html: sample-member.txt scribe.perl
	perl scribe.perl --embed --member $< >$@
sample-team.html: sample-team.txt scribe.perl
	perl scribe.perl --embed --team $< >$@
sample-fancy.html: sample-fancy.txt scribe.perl
	perl scribe.perl --final --embed --fancy  $< >$@


.PHONY: check all samples
