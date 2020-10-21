# spiral-package-simt

This is the SPIRAL package that supports code generation for GPUs

Installation
------------

Clone this repository into the namespaces/packages subdirectory of your SPIRAL
installation tree and rename it to "simt".  For example, from the SPIRAL root
directory:

```
cd namespaces/packages
git clone https://github.com/spiralgen/spiral-package-simt.git simt
```


Examples 
--------

The SPIRAL package FFTX depends on SIMT package in order to generate code for GPUs.

Generically, to use the simt package one would...

```
Load(simt);
Import(simt);

...

```
