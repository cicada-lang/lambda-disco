import { Mod } from "../mod"

export abstract class Stmt {
  abstract execute(mod: Mod): Promise<void | string>
  abstract undo(mod: Mod): Promise<void>
}
