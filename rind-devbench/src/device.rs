//! What this device is, sent with every run: model, chip, OS, cores, CPU
//! features. Never the device name, serial, UDID or IP.
use serde_json::{Value, json};

#[cfg(target_vendor = "apple")]
fn sysctl_str(name: &str) -> Option<String> {
    let c = std::ffi::CString::new(name).ok()?;
    let mut len: libc::size_t = 0;
    unsafe {
        if libc::sysctlbyname(c.as_ptr(), std::ptr::null_mut(), &mut len, std::ptr::null_mut(), 0) != 0 || len == 0 {
            return None;
        }
        let mut buf = vec![0u8; len];
        if libc::sysctlbyname(c.as_ptr(), buf.as_mut_ptr() as *mut _, &mut len, std::ptr::null_mut(), 0) != 0 {
            return None;
        }
        buf.truncate(len);
        while buf.last() == Some(&0) {
            buf.pop();
        }
        Some(String::from_utf8_lossy(&buf).into_owned())
    }
}

#[cfg(target_vendor = "apple")]
fn sysctl_u64(name: &str) -> Option<u64> {
    let c = std::ffi::CString::new(name).ok()?;
    let mut v: u64 = 0;
    let mut len: libc::size_t = 8;
    let r = unsafe { libc::sysctlbyname(c.as_ptr(), &mut v as *mut u64 as *mut _, &mut len, std::ptr::null_mut(), 0) };
    if r != 0 {
        return None;
    }
    Some(if len == 4 { v & 0xffff_ffff } else { v })
}

fn slug(s: &str) -> String {
    let mut o = String::new();
    for ch in s.to_lowercase().chars() {
        if ch.is_ascii_alphanumeric() {
            o.push(ch)
        } else if !o.ends_with('-') {
            o.push('-')
        }
    }
    o.trim_matches('-').to_string()
}

#[cfg(target_vendor = "apple")]
pub fn capabilities() -> Value {
    let machine = sysctl_str("hw.machine").unwrap_or_default();
    let model = sysctl_str("hw.model").unwrap_or_default();
    // iOS reports the product id in hw.machine (iPad16,6); macOS in hw.model.
    let product = if machine.contains(',') { machine.clone() } else { model.clone() };
    let chip = sysctl_str("machdep.cpu.brand_string").filter(|s| !s.is_empty()).unwrap_or_else(|| {
        match product.as_str() {
            "iPad16,3" | "iPad16,4" | "iPad16,5" | "iPad16,6" => "Apple M4",
            "iPad16,1" | "iPad16,2" => "Apple A17 Pro",
            "iPad14,8" | "iPad14,9" | "iPad14,10" | "iPad14,11" => "Apple M2",
            "iPad13,4" | "iPad13,5" | "iPad13,6" | "iPad13,7" | "iPad13,8" | "iPad13,9" | "iPad13,10" | "iPad13,11" | "iPad13,16" | "iPad13,17" => "Apple M1",
            _ => "Apple (unknown chip)",
        }
        .to_string()
    });
    let feats = [
        "FEAT_AES", "FEAT_PMULL", "FEAT_SHA1", "FEAT_SHA256", "FEAT_SHA512", "FEAT_SHA3", "FEAT_DotProd",
        "FEAT_BF16", "FEAT_I8MM", "FEAT_SME", "FEAT_SME2", "FEAT_DIT", "FEAT_SB", "FEAT_LSE", "FEAT_RDM",
    ];
    let features: Vec<&str> = feats.iter().copied().filter(|f| sysctl_u64(&format!("hw.optional.arm.{f}")) == Some(1)).collect();
    let osv = sysctl_str("kern.osproductversion").unwrap_or_default();
    let os = if cfg!(target_os = "ios") { format!("iPadOS/iOS {osv}") } else { format!("macOS {osv}") };
    json!({
        "platform": if cfg!(target_os = "ios") { "ios" } else { "macos" },
        "product": product, "board": model, "cpu": chip, "os": os,
        "host_slug": slug(&format!("{chip} {product}")),
        "arch": std::env::consts::ARCH,
        "cores": {"logical": sysctl_u64("hw.ncpu"), "p": sysctl_u64("hw.perflevel0.physicalcpu"), "e": sysctl_u64("hw.perflevel1.physicalcpu")},
        "ram_bytes": sysctl_u64("hw.memsize"),
        "features": features,
    })
}

#[cfg(target_os = "android")]
pub fn capabilities() -> Value {
    let prop = |k: &str| {
        std::process::Command::new("/system/bin/getprop")
            .arg(k)
            .output()
            .ok()
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
            .unwrap_or_default()
    };
    let cpuinfo = std::fs::read_to_string("/proc/cpuinfo").unwrap_or_default();
    let features: Vec<String> = cpuinfo
        .lines()
        .find(|l| l.starts_with("Features"))
        .and_then(|l| l.split_once(':'))
        .map(|(_, f)| f.split_whitespace().map(String::from).collect())
        .unwrap_or_default();
    let mut parts: Vec<String> = cpuinfo
        .lines()
        .filter(|l| l.starts_with("CPU part"))
        .filter_map(|l| l.split_once(':').map(|(_, v)| v.trim().to_string()))
        .collect();
    let n = parts.len();
    parts.dedup();
    let mut freqs = vec![];
    for i in 0..n.max(1) {
        if let Ok(f) = std::fs::read_to_string(format!("/sys/devices/system/cpu/cpu{i}/cpufreq/cpuinfo_max_freq")) {
            freqs.push(f.trim().parse::<u64>().unwrap_or(0));
        }
    }
    let soc = format!("{} {}", prop("ro.soc.manufacturer"), prop("ro.soc.model")).trim().to_string();
    let model = format!("{} {}", prop("ro.product.manufacturer"), prop("ro.product.model"));
    json!({
        "platform": "android", "product": model, "board": prop("ro.board.platform"),
        "cpu": if soc.is_empty() { prop("ro.hardware") } else { soc.clone() },
        "os": format!("Android {} (SDK {})", prop("ro.build.version.release"), prop("ro.build.version.sdk")),
        "host_slug": slug(&format!("{} {}", if soc.is_empty() { "android" } else { &soc }, prop("ro.product.model"))),
        "arch": std::env::consts::ARCH,
        "cores": {"logical": n, "cpu_parts": parts, "max_khz": freqs},
        "features": features,
    })
}

#[cfg(not(any(target_vendor = "apple", target_os = "android")))]
pub fn capabilities() -> Value {
    json!({"platform": std::env::consts::OS, "arch": std::env::consts::ARCH, "cpu": "unknown", "os": std::env::consts::OS, "host_slug": "host"})
}
