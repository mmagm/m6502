formal_targets := $(patsubst formal/%.py, %, $(wildcard formal/formal_*.py))

.PHONY: formal

formal: $(formal_targets)

formal_%: formal/sby/%_bmc/PASS
	$(info $(shell date '+%d %b %Y %H:%M:%S') Verified instruction '$*')

formal/sby/%_bmc/PASS: formal/sby/%.sby
	$(info $(shell date '+%d %b %Y %H:%M:%S') Running formal verification on instruction '$*'...)
	sby -f $< 2>&1 >/dev/null; if [ $$? -ne 0 ]; then \
	echo `date '+%d %b %Y %H:%M:%S'` Formal verification FAILED for instruction \'$*\'; \
	fi

formal/sby/%.sby: formal/sby/%.il formal/formal.sby
	mkdir -p formal/sby
	cat formal/formal.sby | sed --expression='s#rel_file#$*#g' | sed --expression='s#abs_file#formal/sby/$*#g' > $@

formal/sby/%.il: formal/formal_%.py core.py
	python3 core.py --insn $* generate -t il > $@

formal/sby/alu8.il: alu8.py
	python3 alu8.py generate -t il > $@
