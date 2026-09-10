// Hazard: two-word keywords (`use case`, `analysis case`) — the fused
// single-word spellings from other tools are not names in a definition
// position and must be rejected with recovery at the member boundary.
package P {
    usecase Broken; //~ ERROR expected `;` or `{`, found `Broken`
    part def Fine1;
    use case Works;
    analysiscase A2; //~ ERROR expected `;` or `{`, found `A2`
    part def Fine2;
}
