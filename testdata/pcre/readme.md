# PCRE2 Testdata

The Regex library is tested with the [testdata](https://github.com/PCRE2Project/pcre2/tree/master)
of PCRE2 library.

* testinput1 is from [PCRE2 library](https://github.com/PCRE2Project/pcre2/blob/master/testdata/testinput1),
* tests for variable length positive lookbehind are removed from testinput1,
* perltest.sh is from [PCRE2 library](https://github.com/PCRE2Project/pcre2/blob/master/perltest.sh),
* perltest.sh is slightly changed to generate json output,
* json is generated with the cmd *./create-json.sh testinput1 > testresult1.json*.
