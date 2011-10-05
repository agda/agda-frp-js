SRC_JS = require agda.frp agda.frp.main agda.frp.signal agda.frp.time agda.frp.taskqueue agda.mixin agda.box agda.array agda.keys agda.object

DEMO_AGDA = FRP.JS.Demo.Hello FRP.JS.Demo.Clock FRP.JS.Demo.Button FRP.JS.Demo.HRef FRP.JS.Demo.Calculator FRP.JS.Demo.Geolocation
DEMO_HTML = hello clock button href calculator geolocation
DEMO_CSS = demo
DEMO_PNG = alu

TEST_AGDA = FRP.JS.Test
TEST_HTML = tests
TEST_JS = qunit agda.qunit
TEST_CSS = qunit

DIST_FILES = $(addprefix dist/, \
  $(addsuffix .js,$(SRC_JS)) \
  $(addprefix jAgda.,$(addsuffix .js,$(DEMO_AGDA))) \
  $(addsuffix .html,$(DEMO_HTML)) \
  $(addsuffix .css,$(DEMO_CSS)) \
  $(addsuffix .png,$(DEMO_PNG)))

TEST_FILES = $(addprefix build/, \
  $(addsuffix .js,$(SRC_JS)) \
  $(addprefix jAgda.,$(addsuffix .js,$(TEST_AGDA))) \
  $(addsuffix .js,$(TEST_JS)) \
  $(addsuffix .html,$(TEST_HTML)) \
  $(addsuffix .css,$(TEST_CSS)))

dist/:
	mkdir dist

dist/%.html: demo/html/%.html
	cp $< $@

dist/%.css: demo/css/%.css
	cp $< $@

dist/%.png: demo/images/%.png
	cp $< $@

dist/%.js: src/js/%.js
	cp $< $@

.SECONDEXPANSION:
dist/jAgda.%.js: demo/agda/$$(subst .,/,$$*).agda src/agda/FRP/JS/*.agda src/agda/FRP/JS/*/*.agda demo/agda/FRP/JS/Demo/*.agda demo/agda/FRP/JS/Demo/*/*.agda
	agda -i src/agda -i demo/agda --js --compile-dir dist $<

build/:
	mkdir build

build/%.html: test/html/%.html
	cp $< $@

build/%.css: test/css/%.css
	cp $< $@

build/%.js: src/js/%.js
	cp $< $@

build/%.js: test/js/%.js
	cp $< $@

.SECONDEXPANSION:
build/jAgda.%.js: test/agda/$$(subst .,/,$$*).agda src/agda/FRP/JS/*.agda src/agda/FRP/JS/*/*.agda test/agda/FRP/JS/Test/*.agda
	agda -i src/agda -i test/agda --js --compile-dir build $<

demos: dist/ $(DIST_FILES)

tests: build/ $(TEST_FILES)

veryclean:
	rm -rf dist build

all: demos tests

