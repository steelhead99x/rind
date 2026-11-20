//! JNI entry points for io.github.steelhead99x.rindbench.Native.
use jni::JNIEnv;
use jni::objects::{JClass, JString};
use jni::sys::{jint, jstring};

fn s(env: &mut JNIEnv, v: String) -> jstring {
    env.new_string(v).map(|j| j.into_raw()).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "system" fn Java_io_github_steelhead99x_rindbench_Native_catalog(mut env: JNIEnv, _c: JClass) -> jstring {
    let v = crate::catalog().to_string();
    s(&mut env, v)
}

#[unsafe(no_mangle)]
pub extern "system" fn Java_io_github_steelhead99x_rindbench_Native_device(mut env: JNIEnv, _c: JClass) -> jstring {
    let v = crate::device::capabilities().to_string();
    s(&mut env, v)
}

#[unsafe(no_mangle)]
pub extern "system" fn Java_io_github_steelhead99x_rindbench_Native_start(mut env: JNIEnv, _c: JClass, cfg: JString) -> jint {
    let cfg: String = match env.get_string(&cfg) {
        Ok(v) => v.into(),
        Err(_) => return 2,
    };
    match crate::start(&cfg) {
        Ok(()) => 0,
        Err(e) => {
            crate::set_status(|st| st["start_error"] = serde_json::json!(e));
            1
        }
    }
}

#[unsafe(no_mangle)]
pub extern "system" fn Java_io_github_steelhead99x_rindbench_Native_status(mut env: JNIEnv, _c: JClass) -> jstring {
    let v = crate::status().to_string();
    s(&mut env, v)
}

#[unsafe(no_mangle)]
pub extern "system" fn Java_io_github_steelhead99x_rindbench_Native_setenv(mut env: JNIEnv, _c: JClass, k: JString, v: JString) {
    let k: String = match env.get_string(&k) { Ok(s) => s.into(), Err(_) => return };
    let v: String = match env.get_string(&v) { Ok(s) => s.into(), Err(_) => return };
    // SAFETY: called once at launch, before the catalog or any run reads the environment.
    unsafe { std::env::set_var(k, v) };
}

#[unsafe(no_mangle)]
pub extern "system" fn Java_io_github_steelhead99x_rindbench_Native_stop(_env: JNIEnv, _c: JClass) {
    crate::stop()
}
