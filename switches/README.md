
We use the switches in this folder for compiling coq projects used to train and evaluate RANGO. The projects each switch is used for are listed below. 

## Main Switch
This opam switch is used to compile all of the projects for collecting training data, and is used to compile the following projects in Rango's evaluation:
### eval.opam
| Repo                          | Commit                                   |
|------                         |--------                                  |
| AbsInt/CompCert               | 98323527abda4f6b01ca6a23518907a1272c9021 |
| coq-community/coq-ext-lib     | 00d3f4e2a260c7c23d2c0b9cbc69516f8be4ac92 |
| coq-community/fourcolor       | 43719c0fb5fb6cb0c8fc1c2db09efc632c23df90 |
| coq-community/math-classes    | 6ad1db9fbd646f8daf1568afef230a76a9f58643 |
| coq-community/reglang         | db8be63ec40349e529b6a57c8bcee1acb3f90ceb |
| coq-community/buchberger      | 55ee2e82a05904a7dfb060e558044284abe9c9f5 |
| coq-community/hoare-tut       | 66dfb255c9e8bb49269d83b3577b285288f39928 |
| coq-community/zorns-lemma     | aaf46b0c5f7857ce9211cbaaf36f184ca810e0e8 |
| coq-community/huffman         | 03d40bd01f2bbccf774e369a3d3feaa2b2a5524a |
| thery/PolTac                  | 90c42be344fd778261fd84b065809b2c81938c49 |
| coq-community/dblib           | 25469872c0ba99b046f7e5b8608205eeea5ac077 |
| coq-contribs/zfc              | ede7126560844c381c2b021003a8dbcb0668ecad |


## Other Switches
These switches are used to compile the following "recent projects" -- from after the cutoff of Deepseek Coder

### eval-8.17.opam
| Repo                          | Commit                                   |
| ---                           | ---                                      |
| coq-community/trocq           | d417b00133c457e374a34afca71abb9ccee2c5aa | 
| kaist-cp/smr-verification     | eba45f6be1028cfe0f68c22ad83bd627507a455a |
| Lapin0t/mu-mu-tilde           | f4342676c41a68ed1a068a9e37cddab267f08461 | 

### eval-8.18.opam
| Repo                              | Commit                                   |
| ---                               | ---                                      |
| ccz181078/Coq-BB5                 | 632ba68b03adb27f4f6faaa76b83db934d5ecbba |
| PnVDiscord/PnVRocqLib             | f621247710cd561539dbdbf5c95d56c29ae545c8 |
| thamugadi/semantic-preservation   | 7fa40431d08ab02ee2cf1a120b59039c300eb49e |

### eval-8.19.opam
| Repo                          | Commit                                   | 
| ---                           | ---                                      |
| hferee/UIML                   | 3b0fd30a1657947b762090dc658b771b5a04a062 |
| koka-lang/AddressC            | 854462713f031c29f8abeaec017929a0e4902721 |

