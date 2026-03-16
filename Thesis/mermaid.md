```mermaid
graph TD;
    5.4-->5.1;
    5.4-->5.3;
    5.4-->5.2;

    5.3 o--o 2.6;
    5.2 o--o 2.8;
    5.1 --> 1[[ ]];
    2.8 --> 2.7;
```


set_option trace.Meta.synthInstance true in