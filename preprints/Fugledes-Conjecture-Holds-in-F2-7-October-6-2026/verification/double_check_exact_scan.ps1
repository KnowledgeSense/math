param([Parameter(Mandatory=$true)][string]$DataPath,[Parameter(Mandatory=$true)][string]$OutputDirectory)
$ErrorActionPreference = 'Stop'
$taskSourceHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $DataPath).Hash.ToLowerInvariant()
if ($taskSourceHash -ne 'e51a18c458e1bae995e335e5067b53078e7e8c6901278e755d33c1b281547520') { throw 'Primary data SHA-256 differs' }
New-Item -ItemType Directory -Path $OutputDirectory -Force | Out-Null
Add-Type -TypeDefinition @'
using System;
using System.IO;
using System.IO.Compression;
using System.Text;
using System.Globalization;
public static class FugledeExactRankAudit {
  static int HighestBit(uint x) {
    int p = 0;
    if (x >= 65536u) { x >>= 16; p += 16; }
    if (x >= 256u) { x >>= 8; p += 8; }
    if (x >= 16u) { x >>= 4; p += 4; }
    if (x >= 4u) { x >>= 2; p += 2; }
    if (x >= 2u) p++;
    return p;
  }
  public static string Run(string input, string output) {
    long records = 0, kept = 0;
    long[] counts = new long[33];
    uint[] rows = new uint[32], basis = new uint[32];
    using (FileStream file = File.OpenRead(input))
    using (GZipStream gzip = new GZipStream(file, CompressionMode.Decompress))
    using (StreamReader reader = new StreamReader(gzip, Encoding.ASCII, false, 1048576))
    using (StreamWriter writer = new StreamWriter(output, false, new UTF8Encoding(false))) {
      string line;
      while ((line = reader.ReadLine()) != null) {
        string[] tokens = line.Split((char[])null, StringSplitOptions.RemoveEmptyEntries);
        if (tokens.Length != 32) throw new Exception("Record must contain exactly 32 rows");
        for (int i = 0; i < 32; i++) rows[i] = UInt32.Parse(tokens[i], NumberStyles.AllowHexSpecifier, CultureInfo.InvariantCulture);
        Array.Clear(basis, 0, basis.Length);
        int dimension = 0;
        // Compute the FULL rank: no early rejection at rank eight.
        // Both the base row and base column are 31 (zero based).
        for (int i = 0; i < 32; i++) {
          uint vector = rows[i] ^ rows[31];
          if ((vector & 0x80000000u) != 0) vector ^= UInt32.MaxValue;
          while (vector != 0) {
            int pivot = HighestBit(vector);
            if (basis[pivot] == 0) { basis[pivot] = vector; dimension++; break; }
            vector ^= basis[pivot];
          }
        }
        records++; counts[dimension]++;
        if (dimension <= 7) {
          writer.WriteLine(records + " " + dimension + " " + String.Join(" ",tokens)); kept++;
        }
        if (records % 1000000 == 0) Console.WriteLine("Exact full ranks checked: " + records);
      }
    }
    string[] fields = new string[counts.Length];
    for (int i = 0; i < counts.Length; i++) fields[i] = "\"" + i + "\":" + counts[i];
    return "{\"records\":" + records + ",\"retained\":" + kept + ",\"full_rank_histogram\":{" + String.Join(",",fields) + "}}";
  }
}
'@ -Language CSharp
$taskScanJson = [FugledeExactRankAudit]::Run($DataPath,(Join-Path $OutputDirectory 'exact_rank_le7.txt'))
$taskScanResult = $taskScanJson | ConvertFrom-Json
$taskScanResult | Add-Member -NotePropertyName primary_sha256 -NotePropertyValue $taskSourceHash
$taskScanResult | ConvertTo-Json -Depth 5 | Set-Content -Encoding utf8 -LiteralPath (Join-Path $OutputDirectory 'exact_scan_results.json')
Write-Output ($taskScanResult | ConvertTo-Json -Depth 5)
