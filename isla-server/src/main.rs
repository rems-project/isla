use warp::Filter;

#[tokio::main]
async fn main() {
    let dist = warp::path!("query" / String)
        .map(|arg| {
            println!("query/{}", arg);
            "test".to_string()
        })
        .or(warp::fs::dir("../isla-webui/dist/"));

    warp::serve(dist)
        .run(([127, 0, 0, 1], 3030))
        .await;
}
