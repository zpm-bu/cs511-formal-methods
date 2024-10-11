| **Key** | **Original**                   | **Remapped?**         | **Alt map** | **Action**     |
| :------ | :----------------------------- | :-------------------- | :---------- | :------------- |
| CTRL-A  | repeat last insert             | {Home}                | META-A      | {C-o}(         |
| CTRL-B  | (unused)                       | {Left}                | META-B      | {S-Left}       |
| CTRL-C  | \<Esc\>                        |                       |             |                |
| CTRL-D  | dedent line                    |                       |             |                |
| CTRL-E  | insert same char as below      | {End}                 | META-E      | {C-o})         |
| CTRL-F  | (unused)                       | {Right}               | META-F      | {S-Right}      |
| CTRL-G  | special                        |                       |             |                |
| CTRL-H  | backspace                      | Snip jump -1          |             |                |
| CTRL-I  | tab                            |                       |             |                |
| CTRL-J  | return                         | Snip choice -         |             |                |
| CTRL-K  | digraph                        | Snip choice +         |             |                |
| CTRL-L  | (unused)                       | Snip jump 1           |             |                |
| CTRL-M  | return                         |                       | META-M      | {C-o}^         |
| CTRL-N  | complete, next                 | {Down}                | META-N      | mini.move down |
| CTRL-O  | do one normal mode command     |                       |             |                |
| CTRL-P  | complete, prev                 | {Up}                  | META-P      | mini.move up   |
| CTRL-Q  | literal                        |                       |             |                |
| CTRL-R  | register paste                 |                       |             |                |
| CTRL-S  | (unused)                       | Signature help        |             |                |
| CTRL-T  | indent                         |                       |             |                |
| CTRL-U  | clear line                     |                       |             |                |
| CTRL-V  | literal                        |                       |             |                |
| CTRL-W  | delete word                    |                       |             |                |
| CTRL-X  | trigger completion             |                       |             |                |
| CTRL-Y  | insert same char as above      | Select snip from list |             |                |
| CTRL-Z  | (unused)                       |                       |             |                |
| CTRL-@  | Repeat last insert and \<Esc\> |                       |             |                |
| CTRL-^  | Toggle `:lmap`                 |                       |             |                |
| CTRL-_  |                                |                       |             |                |
| CTRL-]  | expand abbreviation            | Snip expand           |             |                |
| CTRL-\  | change mode                    |                       |             |                |

```lua
vim.keymap.set("i", "<C-a>", "<Home>")
vim.keymap.set("i", "<M-a>", "<C-o>(")
vim.keymap.set("i", "<C-b>", "<Left>")
vim.keymap.set("i", "<M-b>", "<S-Left>")
vim.keymap.set("i", "<M-lt>", "<C-o>1G<Home>")
vim.keymap.set("i", "<M->>", "<C-o>G<End>")
```
