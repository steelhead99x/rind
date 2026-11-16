# ACVP sample vector sets

Sample vector sets from NIST's [ACVP-Server] (`gen-val/json-files/`), the
known-answer sets of the Automated Cryptographic Validation Protocol that
replaced CAVP. Each file is a set's `internalProjection.json`, which holds
its prompts and their answers together.

`admin/sync-acvp` fetches them from the revision it pins, v1.1.0.43
(2026-08-12), and changes them as follows: it keeps only the test groups and
tests whose parameters rind offers, as its filters list, and drops SP
800-106's randomized-hashing groups and tests whose bit `len` is not a whole
number of bytes. AES-CTR's tests carry `payloadLen` instead, so its
bit-length payloads stay, and its test masks them. To update, bump the revision in
`admin/sync-acvp` and rerun it. The tests that read a set fail on any group
they do not expect, so the script's filters are the only place a test is
skipped.

rind-acvp's offline test reads them too, and alone reads the HMAC_DRBG and
RSA key generation sets, which test rind-fips's module.

These are samples whose answers NIST publishes. Passing them is not a
validation: that answers fresh sets from NIST's ACVP server.

## License

ACVP-Server's README carries this notice, which applies to these files:

> NIST-developed software is provided by NIST as a public service. You may
> use, copy, and distribute copies of the software in any medium, provided
> that you keep intact this entire notice. You may improve, modify, and
> create derivative works of the software or any portion of the software,
> and you may copy and distribute such modifications or works. Modified works
> should carry a notice stating that you changed the software and should note
> the date and nature of any such change. Please explicitly acknowledge the
> National Institute of Standards and Technology as the source of the
> software.
>
> NIST-developed software is expressly provided "AS IS." NIST MAKES NO
> WARRANTY OF ANY KIND, EXPRESS, IMPLIED, IN FACT, OR ARISING BY OPERATION OF
> LAW, INCLUDING, WITHOUT LIMITATION, THE IMPLIED WARRANTY OF
> MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, NON-INFRINGEMENT, AND
> DATA ACCURACY. NIST NEITHER REPRESENTS NOR WARRANTS THAT THE OPERATION OF
> THE SOFTWARE WILL BE UNINTERRUPTED OR ERROR-FREE, OR THAT ANY DEFECTS WILL
> BE CORRECTED. NIST DOES NOT WARRANT OR MAKE ANY REPRESENTATIONS REGARDING
> THE USE OF THE SOFTWARE OR THE RESULTS THEREOF, INCLUDING BUT NOT LIMITED
> TO THE CORRECTNESS, ACCURACY, RELIABILITY, OR USEFULNESS OF THE SOFTWARE.
>
> You are solely responsible for determining the appropriateness of using
> and distributing the software and you assume all risks associated with its
> use, including but not limited to the risks and costs of program errors,
> compliance with applicable laws, damage to or loss of data, programs or
> equipment, and the unavailability or interruption of operation. This
> software is not intended to be used in any situation where a failure could
> cause risk of injury or damage to property. The software developed by NIST
> employees is not subject to copyright protection within the United States.

The changes: on 2026-11-09, rind trimmed each set to the groups and tests
it runs, as above, and on 2026-11-14 added the HMAC_DRBG and RSA key
generation sets, trimmed alike. Source: National Institute of Standards and Technology,
[ACVP-Server].

[ACVP-Server]: https://github.com/usnistgov/ACVP-Server
