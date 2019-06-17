# tftp-client-coq

Simple TFTP client written in Coq (with IO handling in OCaml) as an assesment for MIMUW Computer-Aided Verification course.
The implementation should follow [RFC1350](https://tools.ietf.org/html/rfc1350) standard.

### Example usage

Downloading a file
```
ocamlrun main.byte -h 127.0.0.1 -m w file.txt
```

Uploading a file
```
ocamlrun main.byte -h 127.0.0.1 -m r file.txt
```
