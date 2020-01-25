Ghidra printf Function Override Script
======================================

This script analyzes calls to the printf function, checks for format specifiers
and overrides the signature accordingly at the call address.

Currently only compiler specs that pass parameters by register are supported.
All contributions are welcome.
