import SbrClient.FFmpeg.Contracts
import SbrClient.FFmpeg.UpstreamCalls

/-! The concrete independent FFmpeg proof artifacts discharge the complete
interface used by the host application. No new proof axiom is introduced. -/
namespace SbrClient.SbrAPI
open Kraken.Examples.Sbr.SessionBin
variable [CodeEnv]

theorem verifiedCalls (B : SessPlaced) (S : Setup) : Calls S :=
  ⟨Upstream.config_top B S, Upstream.apply_top B S⟩

end SbrClient.SbrAPI
